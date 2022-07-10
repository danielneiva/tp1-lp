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
      Var x  => lookup env x
    | ConI _ => IntT
    | ConB _ => BoolT
    | Let (x, e1, e2) => if ((teval e1 env) = (teval e2 env)) then teval e2 env else raise WrongRetType
    | _ => raise UnknownType;