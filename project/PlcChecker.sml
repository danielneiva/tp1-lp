(* PlcChecker *)

exception EmptySeq
exception UnknownType
exception NotEqTypes
exception WrongRetType
exception DiffBrTypes
exception IfCondNotBool
exception NoMatchResults
exception MatchResTypeDiff
exception MatchCondTypesDiff
exception CallTypeMisM
exception NotFunc
exception ListOutOfRange
exception OpNonList


fun teval (e:expr) (env: pclType env) : pclType =
    case e of
      Var x   => lookup env x  (*1*)
    | ConI _  => IntT          (*2*)
    | ConB _  => BoolT         (*3 e 4*)
    | List [] => ListT []      (*5*)
    | List e  =>               (*6*)
          case e of
          (hd::tl) => teval hd env
          | _ => raise OpNonList
    | ESeq e  => e             (*7*)
    | ESeq _  => raise EmptySeq
    | Let (x, e1, e2) =>       (*8*)
        if 
          ((teval e1 env) = (teval e2 env)) 
        then 
          teval e2 env 
        else 
          raise WrongRetType
    | Letrec (f, t, x, t1, e1, e2) => (*9*)
        let
          val te1 = teval e1 ((f, (FunT(t, t1)))::(x, t)::p)
          val t2  = teval e2 ((f, (FunT(t, t1)))::p)
        in
          if 
            t1 = te1 
          then 
            t2 
          else 
            raise WrongRetType
        end
    | Anon (plcType, s, e) =>         (*10*)
        if 
          ((teval e env) = plcType) 
        then 
          teval e env 
        else 
          raise WrongRetType
    | Call(e2, e1) =>                 (*11*)
        let
          fun aux (FunT(s, t)) = t
            | aux _ = raise NotFunc
          val t1 = teval e1 env
          val t2 = aux(teval e2 env)
        in
          if 
            teval e2 env = FunT(t1, t2) 
          then 
            t2 
          else raise CallTypeMisM
        end
    | If (t1, t2, t3) =>  if ((teval t1 env) = BoolT)    (*12*)
                          then 
                            if ((teval t2 env) = (teval t3 env))
                              then
                                teval t2 env
                              else
                                raise DiffBrTypes
                          else 
                            raise IfCondNotBool
    | Match(e, l) =>                                      (*13*)
        let
          fun aux [] env = raise NoMatchResults
            | aux ((NONE, ri)::[]) env = teval ri p
            | aux ((SOME ei, ri)::[]) env = 
                if 
                  teval ei env = teval e env 
                then 
                  teval ri env 
                else 
                  raise MatchCondTypesDiff
            | aux ((NONE, ri)::(en, rn)::t) env = 
                if 
                  teval ri env = teval rn env 
                then 
                  aux ((en, rn)::t) env 
                else 
                  raise MatchResTypeDiff
            | aux ((SOME ei, ri)::(en, rn)::t) env = 
                if 
                  teval ei env <> teval e env 
                then 
                  raise MatchCondTypesDiff 
                else if 
                  teval ri env = teval rn env 
                then  
                  aux ((en, rn)::t) env 
                else 
                  raise MatchResTypeDiff
        in
          aux l env
        end
    | Prim1 (s, e) => 
            let
              val ee = teval e env
            in
              case s of
                  "!"     => if ((ee) = BoolT) then ee else raise WrongRetType  (*14*)
                  | "-"   => if ((ee) = IntT) then ee else raise WrongRetType   (*15*)
                  | "hd"  =>                                                    (*16*)
                        let                                             
                          val evaltype = ee
                        in
                          case evaltype of
                            ListT(types) => evaltype
                            | _ => raise WrongRetType
                        end
                  | "tl" =>                                                      (*17*)
                        let
                          val evaltype = ee
                        in
                          case evaltype of
                            ListT(types) => evaltype
                            | _ => raise WrongRetType
                        end
                  | "ise" =>                                                     (*18*)
                        let                
                          val evaltype = ee
                        in
                          case evaltype of
                            ListT(types) => evaltype
                            | _ => raise WrongRetType
                        end
                  | "print" => ee                                                (*19*)
                  | _ => raise UnknownType
            end
    | Prim2 (string, e1, e2) => 
          let
              val ee1 = teval e1 env;
              val ee2 = teval e2 env
          in case string of
                ("&&") =>    (*20*)                                           
                if 
                  ((ee1 = ee2) andalso (ee1 = BoolT)) 
                then 
                  BoolT 
                else 
                  raise NotEqTypes
              | ("::") =>   (*21*)  
                if 
                  ((ee1 = ee2) andalso (ee1 = BoolT)) 
                then 
                  ee1 
                else 
                  raise NotEqTypes
              | ("+") =>    (*22*)  
                if 
                  ((ee1 = ee2) andalso (ee1 = IntT)) 
                then 
                  IntT 
                else 
                  raise NotEqTypes
              | ("-") =>    (*22*)  
                if 
                  ((ee1 = ee2) andalso (ee1 = IntT)) 
                then 
                  IntT 
                else raise NotEqTypes
              | ("/") =>    (*22*)
                if 
                  ((ee1 = ee2) andalso (ee1 = IntT)) 
                then 
                  IntT 
                else 
                  raise NotEqTypes
              | ("*") =>    (*22*)
                if 
                  ((ee1 = ee2) andalso (ee1 = IntT)) 
                then 
                  IntT 
                else 
                  raise NotEqTypes
              | ("<") =>    (*23*)
                if 
                  ((ee1 = ee2) andalso (ee1 = IntT)) 
                then 
                  BoolT 
                else 
                  raise NotEqTypes
              | ("<=") =>   (*23*) 
                if 
                  ((ee1 = ee2) andalso (ee1 = IntT)) 
                then 
                  BoolT 
                else 
                  raise NotEqTypes
              | ("=") =>    (*24*) 
                if 
                  (ee1 = ee2) 
                then 
                  BoolT 
                else 
                  raise NotEqTypes
              | ("!=") =>   (*24*)  
                if 
                  (ee1 = ee2) 
                then 
                  BoolT 
                else 
                  raise NotEqTypes
              | (";") =>    (*26*) 
                if 
                  (ee1 = ee2) 
                then 
                  ee1 
                else 
                  raise NotEqTypes
              | _ => raise UnknownType
    | Item (i, List []) => raise ListOutOfRange (* 25 *)
    | Item (1, List (h::t)) => teval h env
    | Item (i, List (h::t)) => teval (Item (i-1, (List t))) env
    | Item (i, e) => 
        let 
          val t = teval e env
          fun aux i (ListT []) = raise ListOutOfRange
            | aux 1 (ListT (h::t)) = h
            | aux i (ListT (h::t)) = aux (i-1) (ListT t)
        in 
          if 
            isListType t 
          then 
            aux i t 
          else 
            raise OpNonList 
        end
    | _ => raise UnknownType;