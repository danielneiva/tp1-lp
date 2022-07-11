(* PlcInterp *)

exception Impossible
exception HDEmptySeq
exception TLEmptySeq
exception ValueNotFoundInMatch
exception NotAFunc

fun eval (e:expr) (env:plcVal env) : plcVal =
  case e of
	  Var x => lookup env x
    | ConI i => IntV i
    | ConB b => BoolV b
	| List(i) =>
      let
        fun evalList (i:expr list) (st:plcVal env) : plcVal list =
          case i of
            [] => []
          | xs::t => (eval xs env)::(evalList t env)
      in
        ListV (evalList i env)
      end
    | ESeq t => SeqV []
    | Let (x, e1, e2) => eval e2 ((x, (eval e1 env))::env)
    | Letrec(funcname, vartype, varname, functype, funcbody, prog) =>
      eval prog ((funcname, Clos (funcname, varname, funcbody, env))::env)
    | Anon(vartype, varname, funcbody) => Clos("", varname, funcbody, env)
	| Call (e2, e1) =>
        let 
			val func = eval e2 env 
		in
          case func of
            Clos(f, x, e, s) =>
            	let
                	val v = eval e1 env
                	val env1 = ((x, v)::(f, func)::s)
              	in
                	eval e env1
              	end
            | _ => raise NotAFunc
        end
	| If(c, texp, elexp) =>
      let
        val test = eval c env
      in
        case test of
          (BoolV result) => if result then (eval texp env) else (eval elexp env)
        | _ => raise Impossible
      end
    | Match(e, options) =>
      let
        val what = eval e env;
        fun tryMatch (next::rest) : plcVal =
            (case next of
              (SOME(condexp), option) =>
                let
                  val cond = eval condexp env
                in
                  if what = cond then eval option env else tryMatch rest
                end
            | (NONE, option) => eval option env)
          | tryMatch [] = raise ValueNotFoundInMatch;
      in
        tryMatch options
      end
	| Prim1 (oper, e) =>
		let
        	val value = eval e env
      	in
			case oper of
				"!" => (case value of BoolV v => BoolV (not v)
					| _ => raise Impossible)
				| "-" => (case value of IntV i => IntV (~ i)
					| _ => raise Impossible)
				| "hd" => (case value of SeqV (xs::t) => xs
					| SeqV ([]) => raise HDEmptySeq
					| _ => raise Impossible)
				| "tl" => (case value of SeqV (xs::t) => SeqV t
					| SeqV ([]) => raise TLEmptySeq
					| _ => raise Impossible)
				| "ise" => (case value of SeqV ([]) => BoolV true
					| SeqV (xs::t) => BoolV false
					| _ => raise Impossible)
				| "print" => (print ((val2string value) ^ "\n"); ListV [])
				| _ => raise Impossible
      	end
    | Prim2(oper, e1, e2) =>
      	let
			val val1 = eval e1 env;
			val val2 = eval e2 env
      	in
			case oper of
			("&&") =>(case (val1, val2) of (BoolV v1, BoolV v2) => BoolV (v1 andalso v2)
				| _ => raise Impossible)
			| ("+") => (case (val1, val2) of (IntV v1, IntV v2) => IntV (v1 + v2)
				| _ => raise Impossible)
			| ("-") => (case (val1, val2) of (IntV v1, IntV v2) => IntV (v1 - v2)
				| _ => raise Impossible)
			| ("*") => (case (val1, val2) of (IntV v1, IntV v2) => IntV (v1 * v2)
				| _ => raise Impossible)
			| ("/") => (case (val1, val2) of (IntV v1, IntV v2) => IntV (v1 div v2)
				| _ => raise Impossible)
			| ("=") => (case (val1, val2) of (BoolV v1, BoolV v2) => BoolV (v1 = v2)
				| (IntV v1, IntV v2) => BoolV (v1 = v2)
				| (ListV v1, ListV v2) => BoolV (v1 = v2)
				| _ => raise Impossible)
			| ("!=") => (case (val1, val2) of (BoolV v1, BoolV v2) => BoolV (v1 <> v2)
				| (IntV v1, IntV v2) => BoolV (v1 <> v2)
				| (ListV v1, ListV v2) => BoolV (v1 <> v2)
				| _ => raise Impossible)
			| ("<") => (case (val1, val2) of (IntV v1, IntV v2) => BoolV (v1 < v2)
				| _ => raise Impossible)
			| ("<=") => (case (val1, val2) of (IntV v1, IntV v2) => BoolV (v1 <= v2)
				| _ => raise Impossible)
			| ("::") => (case val2 of (SeqV []) => SeqV [val1]
				| (SeqV v2) => SeqV (val1::v2)
				| _ => raise Impossible)
			| (";") => val2
			| _ => raise Impossible
      	end
    | Item(index, ite) =>
      let
        val itemeval = eval ite env;
        fun findIndex (curr: int) (xs::t : plcVal list) : plcVal =
            if (curr = index) then xs else if (curr > index) then raise Impossible else findIndex (curr + 1) t
          | findIndex _ [] = raise Impossible
      in
        case itemeval of
          ListV(items) => findIndex 1 items
        | _ => raise Impossible
    	end
	;
