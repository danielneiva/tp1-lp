(* PlcInterp *)

exception Impossible
exception HDEmptySeq
exception TLEmptySeq
exception ValueNotFoundInMatch
exception NotAFunc


fun eval (e:expr) (env:plcVal env) : plcVal =
	case e of
          ConI i => IntV i
		| Var x => lookup env x
        | Prim1(opr, e1) =>
				let
					val v1 = eval e1 env
				in
					case (opr, v1) of
							("-", IntV i) => IntV (~i)
						| ("print", _) =>
										let
											val s = val2string v1
										in
											print(s^"\n"); ListV []
										end
						| _   => raise Impossible
						end
		| _ => raise UnknownType;