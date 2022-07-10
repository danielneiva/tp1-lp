functor PlcParserLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : PlcParser_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct

end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\024\000\002\000\023\000\005\000\022\000\006\000\021\000\
\\009\000\020\000\021\000\019\000\024\000\018\000\026\000\017\000\
\\027\000\016\000\028\000\015\000\030\000\014\000\032\000\013\000\
\\036\000\012\000\042\000\011\000\043\000\010\000\044\000\009\000\
\\045\000\008\000\000\000\
\\001\000\003\000\061\000\044\000\060\000\000\000\
\\001\000\004\000\107\000\007\000\038\000\008\000\037\000\009\000\036\000\
\\010\000\035\000\011\000\034\000\012\000\033\000\013\000\032\000\
\\014\000\031\000\015\000\030\000\017\000\029\000\029\000\028\000\
\\034\000\027\000\037\000\106\000\000\000\
\\001\000\004\000\107\000\037\000\106\000\000\000\
\\001\000\004\000\123\000\007\000\038\000\008\000\037\000\009\000\036\000\
\\010\000\035\000\011\000\034\000\012\000\033\000\013\000\032\000\
\\014\000\031\000\015\000\030\000\017\000\029\000\029\000\028\000\
\\034\000\027\000\000\000\
\\001\000\005\000\022\000\006\000\021\000\009\000\020\000\021\000\019\000\
\\024\000\018\000\026\000\017\000\027\000\016\000\028\000\015\000\
\\030\000\014\000\031\000\049\000\032\000\048\000\034\000\047\000\
\\036\000\012\000\039\000\046\000\040\000\045\000\041\000\044\000\
\\042\000\011\000\043\000\010\000\044\000\009\000\045\000\008\000\000\000\
\\001\000\005\000\022\000\006\000\021\000\009\000\020\000\021\000\019\000\
\\024\000\018\000\026\000\017\000\027\000\016\000\028\000\015\000\
\\030\000\014\000\032\000\013\000\036\000\012\000\038\000\121\000\
\\042\000\011\000\043\000\010\000\044\000\009\000\045\000\008\000\000\000\
\\001\000\005\000\022\000\006\000\021\000\009\000\020\000\021\000\019\000\
\\024\000\018\000\026\000\017\000\027\000\016\000\028\000\015\000\
\\030\000\014\000\032\000\013\000\036\000\012\000\042\000\011\000\
\\043\000\010\000\044\000\009\000\045\000\008\000\000\000\
\\001\000\007\000\038\000\008\000\037\000\009\000\036\000\010\000\035\000\
\\011\000\034\000\012\000\033\000\013\000\032\000\014\000\031\000\
\\015\000\030\000\017\000\029\000\020\000\080\000\029\000\028\000\
\\031\000\079\000\034\000\027\000\000\000\
\\001\000\007\000\038\000\008\000\037\000\009\000\036\000\010\000\035\000\
\\011\000\034\000\012\000\033\000\013\000\032\000\014\000\031\000\
\\015\000\030\000\017\000\029\000\022\000\086\000\029\000\028\000\
\\034\000\027\000\000\000\
\\001\000\007\000\038\000\008\000\037\000\009\000\036\000\010\000\035\000\
\\011\000\034\000\012\000\033\000\013\000\032\000\014\000\031\000\
\\015\000\030\000\017\000\029\000\023\000\122\000\029\000\028\000\
\\034\000\027\000\000\000\
\\001\000\007\000\038\000\008\000\037\000\009\000\036\000\010\000\035\000\
\\011\000\034\000\012\000\033\000\013\000\032\000\014\000\031\000\
\\015\000\030\000\017\000\029\000\025\000\085\000\029\000\028\000\
\\034\000\027\000\000\000\
\\001\000\007\000\038\000\008\000\037\000\009\000\036\000\010\000\035\000\
\\011\000\034\000\012\000\033\000\013\000\032\000\014\000\031\000\
\\015\000\030\000\017\000\029\000\029\000\028\000\034\000\027\000\
\\035\000\142\000\046\000\142\000\000\000\
\\001\000\007\000\038\000\008\000\037\000\009\000\036\000\010\000\035\000\
\\011\000\034\000\012\000\033\000\013\000\032\000\014\000\031\000\
\\015\000\030\000\017\000\127\000\029\000\028\000\034\000\027\000\000\000\
\\001\000\007\000\038\000\008\000\037\000\009\000\036\000\010\000\035\000\
\\011\000\034\000\012\000\033\000\013\000\032\000\014\000\031\000\
\\015\000\030\000\017\000\130\000\029\000\028\000\034\000\027\000\000\000\
\\001\000\007\000\038\000\008\000\037\000\009\000\036\000\010\000\035\000\
\\011\000\034\000\012\000\033\000\013\000\032\000\014\000\031\000\
\\015\000\030\000\017\000\139\000\029\000\028\000\034\000\027\000\000\000\
\\001\000\012\000\094\000\000\000\
\\001\000\012\000\113\000\000\000\
\\001\000\012\000\136\000\018\000\077\000\000\000\
\\001\000\016\000\126\000\000\000\
\\001\000\018\000\077\000\020\000\104\000\031\000\103\000\000\000\
\\001\000\018\000\077\000\020\000\104\000\031\000\103\000\034\000\076\000\000\000\
\\001\000\018\000\077\000\033\000\100\000\000\000\
\\001\000\018\000\077\000\034\000\076\000\000\000\
\\001\000\018\000\077\000\044\000\110\000\000\000\
\\001\000\018\000\128\000\000\000\
\\001\000\019\000\087\000\000\000\
\\001\000\031\000\078\000\000\000\
\\001\000\031\000\091\000\032\000\082\000\034\000\047\000\039\000\046\000\
\\040\000\045\000\041\000\044\000\000\000\
\\001\000\031\000\102\000\000\000\
\\001\000\031\000\112\000\000\000\
\\001\000\031\000\116\000\000\000\
\\001\000\032\000\059\000\000\000\
\\001\000\032\000\082\000\034\000\047\000\039\000\046\000\040\000\045\000\
\\041\000\044\000\000\000\
\\001\000\033\000\095\000\000\000\
\\001\000\033\000\096\000\000\000\
\\001\000\035\000\075\000\000\000\
\\001\000\044\000\062\000\000\000\
\\001\000\044\000\093\000\000\000\
\\001\000\045\000\063\000\000\000\
\\001\000\046\000\000\000\000\000\
\\142\000\007\000\038\000\008\000\037\000\009\000\036\000\010\000\035\000\
\\011\000\034\000\012\000\033\000\013\000\032\000\014\000\031\000\
\\015\000\030\000\017\000\029\000\029\000\028\000\034\000\027\000\000\000\
\\143\000\000\000\
\\144\000\000\000\
\\145\000\000\000\
\\146\000\000\000\
\\147\000\005\000\022\000\032\000\013\000\036\000\012\000\042\000\011\000\
\\043\000\010\000\044\000\009\000\045\000\008\000\000\000\
\\148\000\005\000\022\000\032\000\013\000\036\000\012\000\042\000\011\000\
\\043\000\010\000\044\000\009\000\045\000\008\000\000\000\
\\149\000\007\000\038\000\008\000\037\000\009\000\036\000\010\000\035\000\
\\011\000\034\000\012\000\033\000\013\000\032\000\014\000\031\000\
\\015\000\030\000\029\000\028\000\034\000\027\000\000\000\
\\150\000\000\000\
\\151\000\034\000\027\000\000\000\
\\152\000\010\000\035\000\011\000\034\000\034\000\027\000\000\000\
\\153\000\034\000\027\000\000\000\
\\154\000\034\000\027\000\000\000\
\\155\000\034\000\027\000\000\000\
\\156\000\034\000\027\000\000\000\
\\157\000\008\000\037\000\009\000\036\000\010\000\035\000\011\000\034\000\
\\012\000\033\000\013\000\032\000\014\000\031\000\015\000\030\000\
\\029\000\028\000\034\000\027\000\000\000\
\\158\000\010\000\035\000\011\000\034\000\034\000\027\000\000\000\
\\159\000\010\000\035\000\011\000\034\000\034\000\027\000\000\000\
\\160\000\034\000\027\000\000\000\
\\161\000\034\000\027\000\000\000\
\\162\000\008\000\037\000\009\000\036\000\010\000\035\000\011\000\034\000\
\\014\000\031\000\015\000\030\000\029\000\028\000\034\000\027\000\000\000\
\\163\000\008\000\037\000\009\000\036\000\010\000\035\000\011\000\034\000\
\\014\000\031\000\015\000\030\000\029\000\028\000\034\000\027\000\000\000\
\\164\000\008\000\037\000\009\000\036\000\010\000\035\000\011\000\034\000\
\\029\000\028\000\034\000\027\000\000\000\
\\165\000\008\000\037\000\009\000\036\000\010\000\035\000\011\000\034\000\
\\029\000\028\000\034\000\027\000\000\000\
\\166\000\008\000\037\000\009\000\036\000\010\000\035\000\011\000\034\000\
\\029\000\028\000\034\000\027\000\000\000\
\\167\000\007\000\038\000\008\000\037\000\009\000\036\000\010\000\035\000\
\\011\000\034\000\012\000\033\000\013\000\032\000\014\000\031\000\
\\015\000\030\000\017\000\029\000\029\000\028\000\034\000\027\000\000\000\
\\168\000\000\000\
\\169\000\000\000\
\\170\000\000\000\
\\171\000\000\000\
\\172\000\000\000\
\\173\000\000\000\
\\174\000\000\000\
\\175\000\000\000\
\\176\000\000\000\
\\177\000\000\000\
\\178\000\000\000\
\\179\000\000\000\
\\180\000\000\000\
\\181\000\000\000\
\\182\000\007\000\038\000\008\000\037\000\009\000\036\000\010\000\035\000\
\\011\000\034\000\012\000\033\000\013\000\032\000\014\000\031\000\
\\015\000\030\000\017\000\029\000\020\000\080\000\029\000\028\000\
\\034\000\027\000\000\000\
\\183\000\000\000\
\\184\000\000\000\
\\185\000\000\000\
\\186\000\007\000\038\000\008\000\037\000\009\000\036\000\010\000\035\000\
\\011\000\034\000\012\000\033\000\013\000\032\000\014\000\031\000\
\\015\000\030\000\017\000\029\000\029\000\028\000\034\000\027\000\000\000\
\\187\000\000\000\
\\188\000\000\000\
\\189\000\000\000\
\\190\000\020\000\111\000\000\000\
\\191\000\000\000\
\\192\000\000\000\
\\193\000\000\000\
\\194\000\000\000\
\\195\000\000\000\
\\196\000\018\000\077\000\000\000\
\\197\000\000\000\
\\198\000\000\000\
\\199\000\000\000\
\\200\000\000\000\
\\201\000\018\000\077\000\020\000\104\000\000\000\
\\202\000\000\000\
\"
val actionRowNumbers =
"\000\000\068\000\047\000\046\000\
\\041\000\042\000\078\000\069\000\
\\077\000\076\000\000\000\005\000\
\\007\000\007\000\007\000\007\000\
\\007\000\007\000\007\000\007\000\
\\032\000\001\000\037\000\075\000\
\\074\000\039\000\007\000\007\000\
\\007\000\007\000\007\000\007\000\
\\007\000\007\000\007\000\007\000\
\\007\000\036\000\092\000\023\000\
\\027\000\008\000\098\000\097\000\
\\096\000\033\000\005\000\079\000\
\\055\000\054\000\053\000\052\000\
\\011\000\009\000\051\000\050\000\
\\026\000\028\000\032\000\038\000\
\\016\000\034\000\065\000\066\000\
\\063\000\064\000\062\000\061\000\
\\060\000\059\000\058\000\057\000\
\\056\000\070\000\035\000\033\000\
\\072\000\071\000\007\000\022\000\
\\033\000\029\000\021\000\003\000\
\\007\000\007\000\024\000\089\000\
\\030\000\087\000\017\000\032\000\
\\007\000\067\000\031\000\095\000\
\\082\000\081\000\094\000\020\000\
\\093\000\099\000\033\000\049\000\
\\006\000\083\000\010\000\004\000\
\\091\000\033\000\088\000\007\000\
\\019\000\013\000\080\000\101\000\
\\100\000\025\000\085\000\086\000\
\\007\000\073\000\090\000\014\000\
\\033\000\000\000\007\000\048\000\
\\000\000\018\000\012\000\043\000\
\\002\000\044\000\007\000\084\000\
\\015\000\000\000\045\000\040\000"
val gotoT =
"\
\\001\000\139\000\002\000\005\000\003\000\004\000\004\000\003\000\
\\005\000\002\000\006\000\001\000\000\000\
\\000\000\
\\004\000\023\000\006\000\001\000\000\000\
\\004\000\024\000\006\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\037\000\002\000\005\000\003\000\004\000\004\000\003\000\
\\005\000\002\000\006\000\001\000\000\000\
\\003\000\041\000\004\000\003\000\005\000\002\000\006\000\001\000\
\\007\000\040\000\013\000\039\000\014\000\038\000\000\000\
\\003\000\048\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\049\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\050\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\051\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\052\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\053\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\054\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\055\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\010\000\056\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\003\000\062\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\063\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\064\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\065\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\066\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\067\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\068\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\069\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\070\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\071\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\072\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\013\000\079\000\014\000\038\000\000\000\
\\003\000\041\000\004\000\003\000\005\000\002\000\006\000\001\000\
\\007\000\040\000\013\000\082\000\014\000\038\000\015\000\081\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\011\000\088\000\012\000\087\000\013\000\086\000\014\000\038\000\000\000\
\\010\000\090\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\013\000\095\000\014\000\038\000\000\000\
\\000\000\
\\000\000\
\\003\000\097\000\004\000\003\000\005\000\002\000\006\000\001\000\
\\007\000\096\000\000\000\
\\000\000\
\\013\000\099\000\014\000\038\000\015\000\081\000\000\000\
\\000\000\
\\000\000\
\\008\000\103\000\000\000\
\\003\000\106\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\003\000\107\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\010\000\112\000\000\000\
\\003\000\113\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\013\000\116\000\014\000\038\000\015\000\115\000\000\000\
\\000\000\
\\003\000\118\000\004\000\003\000\005\000\002\000\006\000\001\000\
\\009\000\117\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\011\000\122\000\012\000\087\000\013\000\086\000\014\000\038\000\000\000\
\\000\000\
\\003\000\123\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\003\000\127\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\013\000\129\000\014\000\038\000\000\000\
\\001\000\131\000\002\000\005\000\003\000\130\000\004\000\003\000\
\\005\000\002\000\006\000\001\000\000\000\
\\003\000\132\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\000\000\
\\001\000\133\000\002\000\005\000\003\000\130\000\004\000\003\000\
\\005\000\002\000\006\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\008\000\135\000\000\000\
\\000\000\
\\003\000\136\000\004\000\003\000\005\000\002\000\006\000\001\000\000\000\
\\000\000\
\\000\000\
\\001\000\138\000\002\000\005\000\003\000\130\000\004\000\003\000\
\\005\000\002\000\006\000\001\000\000\000\
\\000\000\
\\000\000\
\"
val numstates = 140
val numrules = 61
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle General.Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(List.map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit ->  unit
 | NAT of unit ->  (int) | NAME of unit ->  (string)
 | TYPES of unit ->  (plcType list) | ATOMICTYPE of unit ->  (plcType)
 | TYPE of unit ->  (plcType) | TYPEDVAR of unit ->  (plcType*string)
 | PARAMS of unit ->  ( ( plcType * string )  list)
 | ARGS of unit ->  ( ( plcType * string )  list)
 | CONDEXPR of unit ->  (expr option)
 | MATCHEXPR of unit ->  ( ( expr option * expr )  list)
 | COMPS of unit ->  (expr list) | CONST of unit ->  (expr)
 | APPEXPR of unit ->  (expr) | ATOMICEXPR of unit ->  (expr)
 | EXPR of unit ->  (expr) | DECL of unit ->  (expr)
 | PROG of unit ->  (expr)
end
type svalue = MlyValue.svalue
type result = expr
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 45) => true | _ => false
val showTerminal =
fn (T 0) => "VAR"
  | (T 1) => "FUN"
  | (T 2) => "REC"
  | (T 3) => "END"
  | (T 4) => "FN"
  | (T 5) => "NOT"
  | (T 6) => "AND"
  | (T 7) => "PLUS"
  | (T 8) => "MINUS"
  | (T 9) => "TIMES"
  | (T 10) => "DIV"
  | (T 11) => "EQUAL"
  | (T 12) => "NEQUAL"
  | (T 13) => "LTE"
  | (T 14) => "LT"
  | (T 15) => "COLON"
  | (T 16) => "SEMICOL"
  | (T 17) => "ARROW"
  | (T 18) => "EQARROW"
  | (T 19) => "COMMA"
  | (T 20) => "IF"
  | (T 21) => "THEN"
  | (T 22) => "ELSE"
  | (T 23) => "MATCH"
  | (T 24) => "WITH"
  | (T 25) => "HD"
  | (T 26) => "TL"
  | (T 27) => "ISE"
  | (T 28) => "CONS"
  | (T 29) => "PRINT"
  | (T 30) => "RPAREN"
  | (T 31) => "LPAREN"
  | (T 32) => "RBRACK"
  | (T 33) => "LBRACK"
  | (T 34) => "RBRACE"
  | (T 35) => "LBRACE"
  | (T 36) => "VBAR"
  | (T 37) => "UNDER"
  | (T 38) => "NIL"
  | (T 39) => "BOOL"
  | (T 40) => "INT"
  | (T 41) => "TRUE"
  | (T 42) => "FALSE"
  | (T 43) => "NAME"
  | (T 44) => "NAT"
  | (T 45) => "EOF"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 45) $$ (T 42) $$ (T 41) $$ (T 40) $$ (T 39) $$ (T 38) $$ (T 37)
 $$ (T 36) $$ (T 35) $$ (T 34) $$ (T 33) $$ (T 32) $$ (T 31) $$ (T 30)
 $$ (T 29) $$ (T 28) $$ (T 27) $$ (T 26) $$ (T 25) $$ (T 24) $$ (T 23)
 $$ (T 22) $$ (T 21) $$ (T 20) $$ (T 19) $$ (T 18) $$ (T 17) $$ (T 16)
 $$ (T 15) $$ (T 14) $$ (T 13) $$ (T 12) $$ (T 11) $$ (T 10) $$ (T 9)
 $$ (T 8) $$ (T 7) $$ (T 6) $$ (T 5) $$ (T 4) $$ (T 3) $$ (T 2) $$ (T 
1) $$ (T 0)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.EXPR EXPR1, EXPR1left, EXPR1right)) :: 
rest671)) => let val  result = MlyValue.PROG (fn _ => let val  (EXPR
 as EXPR1) = EXPR1 ()
 in (EXPR)
end)
 in ( LrTable.NT 0, ( result, EXPR1left, EXPR1right), rest671)
end
|  ( 1, ( ( _, ( MlyValue.DECL DECL1, DECL1left, DECL1right)) :: 
rest671)) => let val  result = MlyValue.PROG (fn _ => let val  (DECL
 as DECL1) = DECL1 ()
 in (DECL)
end)
 in ( LrTable.NT 0, ( result, DECL1left, DECL1right), rest671)
end
|  ( 2, ( ( _, ( MlyValue.PROG PROG1, _, PROG1right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR1, _, _)) :: _ :: ( _, ( MlyValue.NAME NAME1, _, _))
 :: ( _, ( _, VAR1left, _)) :: rest671)) => let val  result = 
MlyValue.DECL (fn _ => let val  (NAME as NAME1) = NAME1 ()
 val  (EXPR as EXPR1) = EXPR1 ()
 val  (PROG as PROG1) = PROG1 ()
 in (Let(NAME, EXPR, PROG))
end)
 in ( LrTable.NT 1, ( result, VAR1left, PROG1right), rest671)
end
|  ( 3, ( ( _, ( MlyValue.PROG PROG1, _, PROG1right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR1, _, _)) :: _ :: ( _, ( MlyValue.ARGS ARGS1, _, _))
 :: ( _, ( MlyValue.NAME NAME1, _, _)) :: ( _, ( _, FUN1left, _)) :: 
rest671)) => let val  result = MlyValue.DECL (fn _ => let val  (NAME
 as NAME1) = NAME1 ()
 val  (ARGS as ARGS1) = ARGS1 ()
 val  (EXPR as EXPR1) = EXPR1 ()
 val  (PROG as PROG1) = PROG1 ()
 in (Let (NAME, makeAnon(ARGS, EXPR), PROG))
end)
 in ( LrTable.NT 1, ( result, FUN1left, PROG1right), rest671)
end
|  ( 4, ( ( _, ( MlyValue.PROG PROG1, _, PROG1right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR1, _, _)) :: _ :: ( _, ( MlyValue.TYPE TYPE1, _, _))
 :: _ :: ( _, ( MlyValue.ARGS ARGS1, _, _)) :: ( _, ( MlyValue.NAME 
NAME1, _, _)) :: _ :: ( _, ( _, FUN1left, _)) :: rest671)) => let val 
 result = MlyValue.DECL (fn _ => let val  (NAME as NAME1) = NAME1 ()
 val  (ARGS as ARGS1) = ARGS1 ()
 val  (TYPE as TYPE1) = TYPE1 ()
 val  (EXPR as EXPR1) = EXPR1 ()
 val  (PROG as PROG1) = PROG1 ()
 in (makeFun (NAME, ARGS, TYPE, EXPR, PROG))
end)
 in ( LrTable.NT 1, ( result, FUN1left, PROG1right), rest671)
end
|  ( 5, ( ( _, ( MlyValue.ATOMICEXPR ATOMICEXPR1, ATOMICEXPR1left, 
ATOMICEXPR1right)) :: rest671)) => let val  result = MlyValue.EXPR (fn
 _ => let val  (ATOMICEXPR as ATOMICEXPR1) = ATOMICEXPR1 ()
 in (ATOMICEXPR)
end)
 in ( LrTable.NT 2, ( result, ATOMICEXPR1left, ATOMICEXPR1right), 
rest671)
end
|  ( 6, ( ( _, ( MlyValue.APPEXPR APPEXPR1, APPEXPR1left, 
APPEXPR1right)) :: rest671)) => let val  result = MlyValue.EXPR (fn _
 => let val  (APPEXPR as APPEXPR1) = APPEXPR1 ()
 in (APPEXPR)
end)
 in ( LrTable.NT 2, ( result, APPEXPR1left, APPEXPR1right), rest671)

end
|  ( 7, ( ( _, ( MlyValue.EXPR EXPR3, _, EXPR3right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR2, _, _)) :: _ :: ( _, ( MlyValue.EXPR EXPR1, _, _))
 :: ( _, ( _, IF1left, _)) :: rest671)) => let val  result = 
MlyValue.EXPR (fn _ => let val  EXPR1 = EXPR1 ()
 val  EXPR2 = EXPR2 ()
 val  EXPR3 = EXPR3 ()
 in (If((EXPR1, EXPR2, EXPR3)))
end)
 in ( LrTable.NT 2, ( result, IF1left, EXPR3right), rest671)
end
|  ( 8, ( ( _, ( MlyValue.MATCHEXPR MATCHEXPR1, _, MATCHEXPR1right))
 :: _ :: ( _, ( MlyValue.EXPR EXPR1, _, _)) :: ( _, ( _, MATCH1left, _
)) :: rest671)) => let val  result = MlyValue.EXPR (fn _ => let val  (
EXPR as EXPR1) = EXPR1 ()
 val  (MATCHEXPR as MATCHEXPR1) = MATCHEXPR1 ()
 in ( Match (EXPR, MATCHEXPR))
end)
 in ( LrTable.NT 2, ( result, MATCH1left, MATCHEXPR1right), rest671)

end
|  ( 9, ( ( _, ( MlyValue.EXPR EXPR1, _, EXPR1right)) :: ( _, ( _, 
NOT1left, _)) :: rest671)) => let val  result = MlyValue.EXPR (fn _ =>
 let val  (EXPR as EXPR1) = EXPR1 ()
 in (Prim1 ("!", EXPR))
end)
 in ( LrTable.NT 2, ( result, NOT1left, EXPR1right), rest671)
end
|  ( 10, ( ( _, ( MlyValue.EXPR EXPR1, _, EXPR1right)) :: ( _, ( _, 
MINUS1left, _)) :: rest671)) => let val  result = MlyValue.EXPR (fn _
 => let val  (EXPR as EXPR1) = EXPR1 ()
 in (Prim1 ("-", EXPR))
end)
 in ( LrTable.NT 2, ( result, MINUS1left, EXPR1right), rest671)
end
|  ( 11, ( ( _, ( MlyValue.EXPR EXPR1, _, EXPR1right)) :: ( _, ( _, 
HD1left, _)) :: rest671)) => let val  result = MlyValue.EXPR (fn _ =>
 let val  (EXPR as EXPR1) = EXPR1 ()
 in (Prim1 ("hd", EXPR))
end)
 in ( LrTable.NT 2, ( result, HD1left, EXPR1right), rest671)
end
|  ( 12, ( ( _, ( MlyValue.EXPR EXPR1, _, EXPR1right)) :: ( _, ( _, 
TL1left, _)) :: rest671)) => let val  result = MlyValue.EXPR (fn _ =>
 let val  (EXPR as EXPR1) = EXPR1 ()
 in (Prim1 ("tl", EXPR))
end)
 in ( LrTable.NT 2, ( result, TL1left, EXPR1right), rest671)
end
|  ( 13, ( ( _, ( MlyValue.EXPR EXPR1, _, EXPR1right)) :: ( _, ( _, 
ISE1left, _)) :: rest671)) => let val  result = MlyValue.EXPR (fn _ =>
 let val  (EXPR as EXPR1) = EXPR1 ()
 in (Prim1 ("ise", EXPR))
end)
 in ( LrTable.NT 2, ( result, ISE1left, EXPR1right), rest671)
end
|  ( 14, ( ( _, ( MlyValue.EXPR EXPR1, _, EXPR1right)) :: ( _, ( _, 
PRINT1left, _)) :: rest671)) => let val  result = MlyValue.EXPR (fn _
 => let val  (EXPR as EXPR1) = EXPR1 ()
 in (Prim1 ("print", EXPR))
end)
 in ( LrTable.NT 2, ( result, PRINT1left, EXPR1right), rest671)
end
|  ( 15, ( ( _, ( MlyValue.EXPR EXPR2, _, EXPR2right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR1, EXPR1left, _)) :: rest671)) => let val  result = 
MlyValue.EXPR (fn _ => let val  EXPR1 = EXPR1 ()
 val  EXPR2 = EXPR2 ()
 in (Prim2 ("&&", EXPR1, EXPR2))
end)
 in ( LrTable.NT 2, ( result, EXPR1left, EXPR2right), rest671)
end
|  ( 16, ( ( _, ( MlyValue.EXPR EXPR2, _, EXPR2right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR1, EXPR1left, _)) :: rest671)) => let val  result = 
MlyValue.EXPR (fn _ => let val  EXPR1 = EXPR1 ()
 val  EXPR2 = EXPR2 ()
 in (Prim2 ("+", EXPR1, EXPR2))
end)
 in ( LrTable.NT 2, ( result, EXPR1left, EXPR2right), rest671)
end
|  ( 17, ( ( _, ( MlyValue.EXPR EXPR2, _, EXPR2right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR1, EXPR1left, _)) :: rest671)) => let val  result = 
MlyValue.EXPR (fn _ => let val  EXPR1 = EXPR1 ()
 val  EXPR2 = EXPR2 ()
 in (Prim2 ("-", EXPR1, EXPR2))
end)
 in ( LrTable.NT 2, ( result, EXPR1left, EXPR2right), rest671)
end
|  ( 18, ( ( _, ( MlyValue.EXPR EXPR2, _, EXPR2right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR1, EXPR1left, _)) :: rest671)) => let val  result = 
MlyValue.EXPR (fn _ => let val  EXPR1 = EXPR1 ()
 val  EXPR2 = EXPR2 ()
 in (Prim2 ("*", EXPR1, EXPR2))
end)
 in ( LrTable.NT 2, ( result, EXPR1left, EXPR2right), rest671)
end
|  ( 19, ( ( _, ( MlyValue.EXPR EXPR2, _, EXPR2right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR1, EXPR1left, _)) :: rest671)) => let val  result = 
MlyValue.EXPR (fn _ => let val  EXPR1 = EXPR1 ()
 val  EXPR2 = EXPR2 ()
 in (Prim2 ("/", EXPR1, EXPR2))
end)
 in ( LrTable.NT 2, ( result, EXPR1left, EXPR2right), rest671)
end
|  ( 20, ( ( _, ( MlyValue.EXPR EXPR2, _, EXPR2right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR1, EXPR1left, _)) :: rest671)) => let val  result = 
MlyValue.EXPR (fn _ => let val  EXPR1 = EXPR1 ()
 val  EXPR2 = EXPR2 ()
 in (Prim2 ("=", EXPR1, EXPR2))
end)
 in ( LrTable.NT 2, ( result, EXPR1left, EXPR2right), rest671)
end
|  ( 21, ( ( _, ( MlyValue.EXPR EXPR2, _, EXPR2right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR1, EXPR1left, _)) :: rest671)) => let val  result = 
MlyValue.EXPR (fn _ => let val  EXPR1 = EXPR1 ()
 val  EXPR2 = EXPR2 ()
 in (Prim2 ("!=", EXPR1, EXPR2))
end)
 in ( LrTable.NT 2, ( result, EXPR1left, EXPR2right), rest671)
end
|  ( 22, ( ( _, ( MlyValue.EXPR EXPR2, _, EXPR2right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR1, EXPR1left, _)) :: rest671)) => let val  result = 
MlyValue.EXPR (fn _ => let val  EXPR1 = EXPR1 ()
 val  EXPR2 = EXPR2 ()
 in (Prim2 ("<", EXPR1, EXPR2))
end)
 in ( LrTable.NT 2, ( result, EXPR1left, EXPR2right), rest671)
end
|  ( 23, ( ( _, ( MlyValue.EXPR EXPR2, _, EXPR2right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR1, EXPR1left, _)) :: rest671)) => let val  result = 
MlyValue.EXPR (fn _ => let val  EXPR1 = EXPR1 ()
 val  EXPR2 = EXPR2 ()
 in (Prim2 ("<=", EXPR1, EXPR2))
end)
 in ( LrTable.NT 2, ( result, EXPR1left, EXPR2right), rest671)
end
|  ( 24, ( ( _, ( MlyValue.EXPR EXPR2, _, EXPR2right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR1, EXPR1left, _)) :: rest671)) => let val  result = 
MlyValue.EXPR (fn _ => let val  EXPR1 = EXPR1 ()
 val  EXPR2 = EXPR2 ()
 in (Prim2 ("::", EXPR1, EXPR2))
end)
 in ( LrTable.NT 2, ( result, EXPR1left, EXPR2right), rest671)
end
|  ( 25, ( ( _, ( MlyValue.EXPR EXPR2, _, EXPR2right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR1, EXPR1left, _)) :: rest671)) => let val  result = 
MlyValue.EXPR (fn _ => let val  EXPR1 = EXPR1 ()
 val  EXPR2 = EXPR2 ()
 in (Prim2 (";", EXPR1, EXPR2))
end)
 in ( LrTable.NT 2, ( result, EXPR1left, EXPR2right), rest671)
end
|  ( 26, ( ( _, ( _, _, RBRACK1right)) :: ( _, ( MlyValue.NAT NAT1, _,
 _)) :: _ :: ( _, ( MlyValue.EXPR EXPR1, EXPR1left, _)) :: rest671))
 => let val  result = MlyValue.EXPR (fn _ => let val  (EXPR as EXPR1)
 = EXPR1 ()
 val  (NAT as NAT1) = NAT1 ()
 in (Item (NAT, EXPR))
end)
 in ( LrTable.NT 2, ( result, EXPR1left, RBRACK1right), rest671)
end
|  ( 27, ( ( _, ( MlyValue.CONST CONST1, CONST1left, CONST1right)) :: 
rest671)) => let val  result = MlyValue.ATOMICEXPR (fn _ => let val  (
CONST as CONST1) = CONST1 ()
 in (CONST)
end)
 in ( LrTable.NT 3, ( result, CONST1left, CONST1right), rest671)
end
|  ( 28, ( ( _, ( MlyValue.NAME NAME1, NAME1left, NAME1right)) :: 
rest671)) => let val  result = MlyValue.ATOMICEXPR (fn _ => let val  (
NAME as NAME1) = NAME1 ()
 in (Var(NAME))
end)
 in ( LrTable.NT 3, ( result, NAME1left, NAME1right), rest671)
end
|  ( 29, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( MlyValue.PROG PROG1,
 _, _)) :: ( _, ( _, LBRACE1left, _)) :: rest671)) => let val  result
 = MlyValue.ATOMICEXPR (fn _ => let val  (PROG as PROG1) = PROG1 ()
 in (PROG)
end)
 in ( LrTable.NT 3, ( result, LBRACE1left, RBRACE1right), rest671)
end
|  ( 30, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.EXPR EXPR1,
 _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result
 = MlyValue.ATOMICEXPR (fn _ => let val  (EXPR as EXPR1) = EXPR1 ()
 in (EXPR)
end)
 in ( LrTable.NT 3, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 31, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.COMPS COMPS1
, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result
 = MlyValue.ATOMICEXPR (fn _ => let val  (COMPS as COMPS1) = COMPS1 ()
 in (List COMPS)
end)
 in ( LrTable.NT 3, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 32, ( ( _, ( _, _, END1right)) :: ( _, ( MlyValue.EXPR EXPR1, _,
 _)) :: _ :: ( _, ( MlyValue.ARGS ARGS1, _, _)) :: ( _, ( _, FN1left,
 _)) :: rest671)) => let val  result = MlyValue.ATOMICEXPR (fn _ =>
 let val  (ARGS as ARGS1) = ARGS1 ()
 val  (EXPR as EXPR1) = EXPR1 ()
 in (makeAnon (ARGS, EXPR))
end)
 in ( LrTable.NT 3, ( result, FN1left, END1right), rest671)
end
|  ( 33, ( ( _, ( MlyValue.ATOMICEXPR ATOMICEXPR2, _, ATOMICEXPR2right
)) :: ( _, ( MlyValue.ATOMICEXPR ATOMICEXPR1, ATOMICEXPR1left, _)) :: 
rest671)) => let val  result = MlyValue.APPEXPR (fn _ => let val  
ATOMICEXPR1 = ATOMICEXPR1 ()
 val  ATOMICEXPR2 = ATOMICEXPR2 ()
 in (Call(ATOMICEXPR1, ATOMICEXPR2))
end)
 in ( LrTable.NT 4, ( result, ATOMICEXPR1left, ATOMICEXPR2right), 
rest671)
end
|  ( 34, ( ( _, ( MlyValue.ATOMICEXPR ATOMICEXPR1, _, ATOMICEXPR1right
)) :: ( _, ( MlyValue.APPEXPR APPEXPR1, APPEXPR1left, _)) :: rest671))
 => let val  result = MlyValue.APPEXPR (fn _ => let val  (APPEXPR as 
APPEXPR1) = APPEXPR1 ()
 val  (ATOMICEXPR as ATOMICEXPR1) = ATOMICEXPR1 ()
 in (Call (APPEXPR, ATOMICEXPR))
end)
 in ( LrTable.NT 4, ( result, APPEXPR1left, ATOMICEXPR1right), rest671
)
end
|  ( 35, ( ( _, ( _, TRUE1left, TRUE1right)) :: rest671)) => let val  
result = MlyValue.CONST (fn _ => (ConB(true)))
 in ( LrTable.NT 5, ( result, TRUE1left, TRUE1right), rest671)
end
|  ( 36, ( ( _, ( _, FALSE1left, FALSE1right)) :: rest671)) => let
 val  result = MlyValue.CONST (fn _ => (ConB(false)))
 in ( LrTable.NT 5, ( result, FALSE1left, FALSE1right), rest671)
end
|  ( 37, ( ( _, ( MlyValue.NAT NAT1, NAT1left, NAT1right)) :: rest671)
) => let val  result = MlyValue.CONST (fn _ => let val  (NAT as NAT1)
 = NAT1 ()
 in (ConI(NAT))
end)
 in ( LrTable.NT 5, ( result, NAT1left, NAT1right), rest671)
end
|  ( 38, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( _, LPAREN1left, _))
 :: rest671)) => let val  result = MlyValue.CONST (fn _ => (List []))
 in ( LrTable.NT 5, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 39, ( ( _, ( _, _, RPAREN1right)) :: _ :: _ :: ( _, ( 
MlyValue.TYPE TYPE1, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671))
 => let val  result = MlyValue.CONST (fn _ => let val  (TYPE as TYPE1)
 = TYPE1 ()
 in (ESeq(TYPE))
end)
 in ( LrTable.NT 5, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 40, ( ( _, ( MlyValue.EXPR EXPR2, _, EXPR2right)) :: _ :: ( _, ( 
MlyValue.EXPR EXPR1, EXPR1left, _)) :: rest671)) => let val  result = 
MlyValue.COMPS (fn _ => let val  EXPR1 = EXPR1 ()
 val  EXPR2 = EXPR2 ()
 in (EXPR1 :: EXPR2 :: [])
end)
 in ( LrTable.NT 6, ( result, EXPR1left, EXPR2right), rest671)
end
|  ( 41, ( ( _, ( MlyValue.COMPS COMPS1, _, COMPS1right)) :: _ :: ( _,
 ( MlyValue.EXPR EXPR1, EXPR1left, _)) :: rest671)) => let val  result
 = MlyValue.COMPS (fn _ => let val  (EXPR as EXPR1) = EXPR1 ()
 val  (COMPS as COMPS1) = COMPS1 ()
 in (EXPR :: COMPS)
end)
 in ( LrTable.NT 6, ( result, EXPR1left, COMPS1right), rest671)
end
|  ( 42, ( ( _, ( _, END1left, END1right)) :: rest671)) => let val  
result = MlyValue.MATCHEXPR (fn _ => ([]))
 in ( LrTable.NT 7, ( result, END1left, END1right), rest671)
end
|  ( 43, ( ( _, ( MlyValue.MATCHEXPR MATCHEXPR1, _, MATCHEXPR1right))
 :: ( _, ( MlyValue.EXPR EXPR1, _, _)) :: _ :: ( _, ( 
MlyValue.CONDEXPR CONDEXPR1, _, _)) :: ( _, ( _, VBAR1left, _)) :: 
rest671)) => let val  result = MlyValue.MATCHEXPR (fn _ => let val  (
CONDEXPR as CONDEXPR1) = CONDEXPR1 ()
 val  (EXPR as EXPR1) = EXPR1 ()
 val  (MATCHEXPR as MATCHEXPR1) = MATCHEXPR1 ()
 in ((CONDEXPR, EXPR) :: MATCHEXPR)
end)
 in ( LrTable.NT 7, ( result, VBAR1left, MATCHEXPR1right), rest671)

end
|  ( 44, ( ( _, ( MlyValue.EXPR EXPR1, EXPR1left, EXPR1right)) :: 
rest671)) => let val  result = MlyValue.CONDEXPR (fn _ => let val  (
EXPR as EXPR1) = EXPR1 ()
 in (SOME EXPR)
end)
 in ( LrTable.NT 8, ( result, EXPR1left, EXPR1right), rest671)
end
|  ( 45, ( ( _, ( _, UNDER1left, UNDER1right)) :: rest671)) => let
 val  result = MlyValue.CONDEXPR (fn _ => (NONE))
 in ( LrTable.NT 8, ( result, UNDER1left, UNDER1right), rest671)
end
|  ( 46, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( _, LPAREN1left, _))
 :: rest671)) => let val  result = MlyValue.ARGS (fn _ => ([]))
 in ( LrTable.NT 9, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 47, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.PARAMS 
PARAMS1, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val 
 result = MlyValue.ARGS (fn _ => let val  (PARAMS as PARAMS1) = 
PARAMS1 ()
 in (PARAMS)
end)
 in ( LrTable.NT 9, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 48, ( ( _, ( MlyValue.TYPEDVAR TYPEDVAR1, TYPEDVAR1left, 
TYPEDVAR1right)) :: rest671)) => let val  result = MlyValue.PARAMS (fn
 _ => let val  (TYPEDVAR as TYPEDVAR1) = TYPEDVAR1 ()
 in (TYPEDVAR :: [])
end)
 in ( LrTable.NT 10, ( result, TYPEDVAR1left, TYPEDVAR1right), rest671
)
end
|  ( 49, ( ( _, ( MlyValue.PARAMS PARAMS1, _, PARAMS1right)) :: _ :: (
 _, ( MlyValue.TYPEDVAR TYPEDVAR1, TYPEDVAR1left, _)) :: rest671)) =>
 let val  result = MlyValue.PARAMS (fn _ => let val  (TYPEDVAR as 
TYPEDVAR1) = TYPEDVAR1 ()
 val  (PARAMS as PARAMS1) = PARAMS1 ()
 in (TYPEDVAR :: PARAMS)
end)
 in ( LrTable.NT 10, ( result, TYPEDVAR1left, PARAMS1right), rest671)

end
|  ( 50, ( ( _, ( MlyValue.NAME NAME1, _, NAME1right)) :: ( _, ( 
MlyValue.TYPE TYPE1, TYPE1left, _)) :: rest671)) => let val  result = 
MlyValue.TYPEDVAR (fn _ => let val  (TYPE as TYPE1) = TYPE1 ()
 val  (NAME as NAME1) = NAME1 ()
 in ((TYPE, NAME))
end)
 in ( LrTable.NT 11, ( result, TYPE1left, NAME1right), rest671)
end
|  ( 51, ( ( _, ( MlyValue.ATOMICTYPE ATOMICTYPE1, ATOMICTYPE1left, 
ATOMICTYPE1right)) :: rest671)) => let val  result = MlyValue.TYPE (fn
 _ => let val  (ATOMICTYPE as ATOMICTYPE1) = ATOMICTYPE1 ()
 in (ATOMICTYPE)
end)
 in ( LrTable.NT 12, ( result, ATOMICTYPE1left, ATOMICTYPE1right), 
rest671)
end
|  ( 52, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.TYPES TYPES1
, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result
 = MlyValue.TYPE (fn _ => let val  (TYPES as TYPES1) = TYPES1 ()
 in (ListT TYPES)
end)
 in ( LrTable.NT 12, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 53, ( ( _, ( _, _, RBRACK1right)) :: ( _, ( MlyValue.TYPE TYPE1,
 _, _)) :: ( _, ( _, LBRACK1left, _)) :: rest671)) => let val  result
 = MlyValue.TYPE (fn _ => let val  (TYPE as TYPE1) = TYPE1 ()
 in (SeqT TYPE)
end)
 in ( LrTable.NT 12, ( result, LBRACK1left, RBRACK1right), rest671)

end
|  ( 54, ( ( _, ( MlyValue.TYPE TYPE2, _, TYPE2right)) :: _ :: ( _, ( 
MlyValue.TYPE TYPE1, TYPE1left, _)) :: rest671)) => let val  result = 
MlyValue.TYPE (fn _ => let val  TYPE1 = TYPE1 ()
 val  TYPE2 = TYPE2 ()
 in (FunT (TYPE1, TYPE2))
end)
 in ( LrTable.NT 12, ( result, TYPE1left, TYPE2right), rest671)
end
|  ( 55, ( ( _, ( _, NIL1left, NIL1right)) :: rest671)) => let val  
result = MlyValue.ATOMICTYPE (fn _ => (ListT []))
 in ( LrTable.NT 13, ( result, NIL1left, NIL1right), rest671)
end
|  ( 56, ( ( _, ( _, BOOL1left, BOOL1right)) :: rest671)) => let val  
result = MlyValue.ATOMICTYPE (fn _ => (BoolT))
 in ( LrTable.NT 13, ( result, BOOL1left, BOOL1right), rest671)
end
|  ( 57, ( ( _, ( _, INT1left, INT1right)) :: rest671)) => let val  
result = MlyValue.ATOMICTYPE (fn _ => (IntT))
 in ( LrTable.NT 13, ( result, INT1left, INT1right), rest671)
end
|  ( 58, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.TYPE TYPE1,
 _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result
 = MlyValue.ATOMICTYPE (fn _ => let val  (TYPE as TYPE1) = TYPE1 ()
 in (TYPE)
end)
 in ( LrTable.NT 13, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 59, ( ( _, ( MlyValue.TYPE TYPE2, _, TYPE2right)) :: _ :: ( _, ( 
MlyValue.TYPE TYPE1, TYPE1left, _)) :: rest671)) => let val  result = 
MlyValue.TYPES (fn _ => let val  TYPE1 = TYPE1 ()
 val  TYPE2 = TYPE2 ()
 in (TYPE1 :: TYPE2 :: [])
end)
 in ( LrTable.NT 14, ( result, TYPE1left, TYPE2right), rest671)
end
|  ( 60, ( ( _, ( MlyValue.TYPES TYPES1, _, TYPES1right)) :: _ :: ( _,
 ( MlyValue.TYPE TYPE1, TYPE1left, _)) :: rest671)) => let val  result
 = MlyValue.TYPES (fn _ => let val  (TYPE as TYPE1) = TYPE1 ()
 val  (TYPES as TYPES1) = TYPES1 ()
 in (TYPE :: TYPES)
end)
 in ( LrTable.NT 14, ( result, TYPE1left, TYPES1right), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.PROG x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : PlcParser_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun VAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun FUN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID,p1,p2))
fun REC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun END (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun FN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun NOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun AND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun PLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun MINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun TIMES (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun DIV (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun EQUAL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun NEQUAL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun LTE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun LT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun COLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun SEMICOL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID,p1,p2))
fun ARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID,p1,p2))
fun EQARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID,p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.VOID,p1,p2))
fun IF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID,p1,p2))
fun THEN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.VOID,p1,p2))
fun ELSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.VOID,p1,p2))
fun MATCH (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.VOID,p1,p2))
fun WITH (p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.VOID,p1,p2))
fun HD (p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(
ParserData.MlyValue.VOID,p1,p2))
fun TL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(
ParserData.MlyValue.VOID,p1,p2))
fun ISE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(
ParserData.MlyValue.VOID,p1,p2))
fun CONS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(
ParserData.MlyValue.VOID,p1,p2))
fun PRINT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(
ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 31,(
ParserData.MlyValue.VOID,p1,p2))
fun RBRACK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 32,(
ParserData.MlyValue.VOID,p1,p2))
fun LBRACK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 33,(
ParserData.MlyValue.VOID,p1,p2))
fun RBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 34,(
ParserData.MlyValue.VOID,p1,p2))
fun LBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 35,(
ParserData.MlyValue.VOID,p1,p2))
fun VBAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 36,(
ParserData.MlyValue.VOID,p1,p2))
fun UNDER (p1,p2) = Token.TOKEN (ParserData.LrTable.T 37,(
ParserData.MlyValue.VOID,p1,p2))
fun NIL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 38,(
ParserData.MlyValue.VOID,p1,p2))
fun BOOL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 39,(
ParserData.MlyValue.VOID,p1,p2))
fun INT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 40,(
ParserData.MlyValue.VOID,p1,p2))
fun TRUE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 41,(
ParserData.MlyValue.VOID,p1,p2))
fun FALSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 42,(
ParserData.MlyValue.VOID,p1,p2))
fun NAME (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 43,(
ParserData.MlyValue.NAME (fn () => i),p1,p2))
fun NAT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 44,(
ParserData.MlyValue.NAT (fn () => i),p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 45,(
ParserData.MlyValue.VOID,p1,p2))
end
end
