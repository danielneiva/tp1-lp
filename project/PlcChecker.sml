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


fun isSeqType (SeqT t: plcType) = true
  | isSeqType _ = false;

fun isEqualityType IntT = true
      | isEqualityType BoolT = true
      | isEqualityType (ListT []) = true
      | isEqualityType (ListT (h::[])) = isEqualityType h
      | isEqualityType (ListT (h::t)) = if isEqualityType h then isEqualityType (ListT t) else false
      | isEqualityType (SeqT (t)) = isEqualityType t
      | isEqualityType _ = false;

fun isListType (ListT l) = true
  | isListType _ = false;
      
fun teval (e:expr) (env:plcType env): plcType =
  case e of
      Var x   => lookup env x               (*1*)
    | ConI _  => IntT                       (*2*)
    | ConB _  => BoolT                      (*3 e 4*)
    | List [] => ListT []                   (*5*)
    | List l =>                             (*6*)
        let
          val list = map (fn t => teval t env) l 
        in
          ListT list
        end
    | ESeq e => e                           (*7*)
    | Let (x, e1, e2) =>                    (*8*)
        let
          val t1 = teval e1 env
        in
          teval e2 ((x, t1) :: env)
        end
    | Letrec (f, t, x, t1, e1, e2) =>       (*9*)
        let
          val te1 = teval e1 ((f, (FunT(t, t1)))::(x, t)::env)
          val t2 = teval e2 ((f, (FunT(t, t1)))::env)
        in
          if t1 = te1 then t2 else raise WrongRetType
        end
    | Anon (plcType, s, e) =>                (*10*)
        let
          val t = teval e ((s, plcType)::env)
        in
          FunT(plcType, t)
        end
    | Call(e2, e1) => (*11*)
        let
          fun aux (FunT(s, t)) = t
            | aux _ = raise NotFunc
          val t1 = teval e1 env
          val t2 = aux(teval e2 env)
        in
          if teval e2 env = FunT(t1, t2) then t2 else raise CallTypeMisM
        end
    | If(e, e1, e2) => (*12*)
        let
          val t = teval e env
          val t1 = teval e1 env
          val t2 = teval e2 env
        in
          if t <> BoolT then raise IfCondNotBool else if t1 = t2 then t1 else raise DiffBrTypes
        end
    | Match(e, l) => (* 13 *)
        let
          fun aux [] env = raise NoMatchResults
            | aux ((NONE, ri)::[]) env = teval ri env
            | aux ((SOME ei, ri)::[]) env = if teval ei env = teval e env then teval ri env else raise MatchCondTypesDiff
            | aux ((NONE, ri)::(en, rn)::t) env = if teval ri env = teval rn env then aux ((en, rn)::t) env else raise MatchResTypeDiff
            | aux ((SOME ei, ri)::(en, rn)::t) env = if teval ei env <> teval e env then raise MatchCondTypesDiff else if teval ri env = teval rn env then aux ((en, rn)::t) env else raise MatchResTypeDiff
        in
          aux l env
        end
    | Prim1("!", e) => if teval e env = BoolT then BoolT else raise UnknownType (* 14 *)
    | Prim1("-", e) => if teval e env = IntT then IntT else raise UnknownType (* 15 *)
    | Prim1("hd", e) => (* 16 *)
        let
          fun aux (SeqT tipo) = tipo
            | aux _ = raise UnknownType
          val t = teval e env
        in
          if isSeqType t then aux t else raise UnknownType
        end
    | Prim1("tl", e) => (* 17 *)
        let
          val t = teval e env
        in
          if isSeqType t then t else raise UnknownType
        end
    | Prim1("ise", e) => (* 18 *)
        let
          val t = teval e env
        in
          if isSeqType t then BoolT else raise UnknownType
        end
    | Prim1("print", e) => (* 19 *)
        let
          val t = teval e env
        in
          ListT [] 
        end  
    | Prim2("&&", e1, e2) => (* 20 *)
        let
          val te1 = teval e1 env
          val te2 = teval e2 env
        in
          if te1 = BoolT andalso te2 = BoolT then BoolT else raise UnknownType
        end
    | Prim2("::", e1, e2) => (* 21 *)
        let
          fun aux (SeqT tipo) = tipo
            | aux _ = raise UnknownType
          val t1 = teval e1 env
          val t2 = teval e2 env
        in
          if t1 = (aux t2) then t2 else raise NotEqTypes
        end
    | Prim2("+", e1, e2) => (* 22 *)
        let
          val te1 = teval e1 env
          val te2 = teval e2 env
        in
          if te1 = IntT andalso te2 = IntT then IntT else raise UnknownType
        end
    | Prim2("-", e1, e2) => (* 22 *)
        let
          val te1 = teval e1 env
          val te2 = teval e2 env
        in
          if te1 = IntT andalso te2 = IntT then IntT else raise UnknownType
        end
    | Prim2("*", e1, e2) => (* 22 *)
        let
          val te1 = teval e1 env
          val te2 = teval e2 env
        in
          if te1 = IntT andalso te2 = IntT then IntT else raise UnknownType
        end
    | Prim2("/", e1, e2) => (* 22 *)
        let
          val te1 = teval e1 env
          val te2 = teval e2 env
        in
          if te1 = IntT andalso te2 = IntT then IntT else raise UnknownType
        end
    | Prim2("<", e1, e2) => (* 23 *)
        let
          val te1 = teval e1 env
          val te2 = teval e2 env
        in
          if te1 = IntT andalso te2 = IntT then BoolT else raise UnknownType
        end
    | Prim2("<=", e1, e2) => (* 23 *)
        let
          val te1 = teval e1 env
          val te2 = teval e2 env
        in
          if te1 = IntT andalso te2 = IntT then BoolT else raise UnknownType
        end
    | Prim2("=", e1, e2) => (* 24 *)
        let
          val te1 = teval e1 env
          val te2 = teval e2 env
        in
          if not (isEqualityType te1) orelse not (isEqualityType te2) then raise UnknownType else if te1 = te2 then BoolT else raise NotEqTypes
        end
    | Prim2("!=", e1, e2) => (* 24 *)
        let
          val te1 = teval e1 env
          val te2 = teval e2 env
        in
          if not (isEqualityType te1) orelse not (isEqualityType te2) then raise UnknownType else if te1 = te2 then BoolT else raise NotEqTypes
        end
    | Prim2 (";", e1, e2) => (* 26 *)
        let
          val t1 = teval e1 env
          val t2 = teval e2 env
        in
          t2
        end
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
          if isListType t then aux i t else raise OpNonList 
        end
    
    | _ => raise UnknownType;