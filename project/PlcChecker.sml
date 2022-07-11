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

fun auxSeq (SeqT tipo) = tipo
  | auxSeq _ = raise UnknownType

fun isEqualityType IntT = true
      | isEqualityType BoolT = true
      | isEqualityType (ListT []) = true
      | isEqualityType (ListT (h::[])) = isEqualityType h
      | isEqualityType (ListT (h::t)) = if isEqualityType h then isEqualityType (ListT t) else false
      | isEqualityType (SeqT (t)) = isEqualityType t
      | isEqualityType _ = false;

fun isListType (ListT l) = true
  | isListType _ = false;
      
fun teval (exp:expr) (env:plcType env): plcType =
  case exp of
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
    | ESeq exp => exp                         (*7*)
    | Let (x, exp1, exp2) =>                    (*8*)
        let
          val tExp1 = teval exp1 env
        in
          teval exp2 ((x, tExp1) :: env)
        end
    | Letrec (f, t, x, tExp1, exp1, exp2) =>       (*9*)
        let
          val te1 = teval exp1 ((f, (FunT(t, tExp1)))::(x, t)::env)
          val tExp2 = teval exp2 ((f, (FunT(t, tExp1)))::env)
        in
          if tExp1 = te1 then tExp2 else raise WrongRetType
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
    | Prim1 (s, exp) =>
      let
        val tExp = teval exp env;
      in
        case s of
        ("!") => if tExp = BoolT then BoolT else raise UnknownType
        | ("-") => if tExp = IntT then IntT else raise UnknownType
        | ("hd") => if isSeqType tExp then auxSeq tExp else raise UnknownType
        | ("tl") => if isSeqType tExp then tExp else raise UnknownType
        | ("ise") => if isSeqType tExp then BoolT else raise UnknownType
        | ("print") => ListT []
        | _ => raise UnknownType
      end
    | Prim2 (s, exp1, exp2) =>
      let 
        val tExp1 = teval exp1 env;
        val tExp2 = teval exp2 env
      in
        case s of
          ("&&") => if (tExp1 = BoolT) andalso (tExp2 = BoolT) then BoolT else raise UnknownType
          | ("::") => if (tExp1 = (auxSeq tExp2)) then tExp2 else raise NotEqTypes
          | ("+") => if (tExp1 = IntT) andalso (tExp2 = IntT) then IntT else raise UnknownType 
          | ("-") => if (tExp1 = IntT) andalso (tExp2 = IntT) then IntT else raise UnknownType 
          | ("*") => if (tExp1 = IntT) andalso (tExp2 = IntT) then IntT else raise UnknownType 
          | ("/") => if (tExp1 = IntT) andalso (tExp2 = IntT) then IntT else raise UnknownType 
          | ("<") => if (tExp1 = IntT) andalso (tExp2 = IntT) then BoolT else raise UnknownType 
          | ("<=") => if (tExp1 = IntT) andalso (tExp2 = IntT) then BoolT else raise UnknownType 
          | ("=") => if not (isEqualityType tExp1) orelse not (isEqualityType tExp2) then raise UnknownType else if (tExp1 = tExp2) then BoolT else raise NotEqTypes 
          | ("!=") => if not (isEqualityType tExp1) orelse not (isEqualityType tExp2) then raise UnknownType else if tExp1 = tExp2 then BoolT else raise NotEqTypes 
          | (";") => tExp2
          | _ => raise UnknownType
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
        end;