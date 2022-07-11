(* Plc interpreter main file *)

fun run exp =
    let 
        val typeE  =  type2string(teval exp [])
        val valueE =  val2string(eval  exp []) 
    in
        (valueE)^":"^(typeE)
    end
    handle
         SymbolNotFound         => "Simbolo não encontrado"
       | EmptySeq               => "Sequência de entrada não contém nenhum elemento"
       | UnknownType            => "Tipo desconhecido"
       | NotEqTypes             => "As expressões não possuem o mesmo tipo"
       | WrongRetType           => "O tipo de retorno da função não condiz com o corpo da função."
       | DiffBrTypes            => "Existem divergência de tipo nos branch do IF"
       | IfCondNotBool          => "Condição do IF deve ser booleana"
       | NoMatchResults         => "Não há expressões para que o match seja realizado"
       | MatchResTypeDiff       => "Existe algum caso em match que o tipo é diferente dos demais"
       | MatchCondTypesDiff     => "As expressões passadas para Match devem ser do mesmo tipo"
       | CallTypeMisM           => "A função não suporta o tipo passado"
       | NotFunc                => "A expressão inserida não é uma função"
       | ListOutOfRange         => "O indixe inserido está fora do tamanho da lista"
       | OpNonList              => "A expressão inserida não é uma lista, não é possível acessar o elemento"
        (**Exceptions from PlcInterp.sml**)
       | Impossible             => "Impossível avaliar a expressão"
       | HDEmptySeq             => "HD chamado em uma sequência vazia"
       | TLEmptySeq             => "TL chamado em uma sequência vazia"
       | ValueNotFoundInMatch   => "Valor não encontrado no Match"
       | NotAFunc               => "A expressão inserida não é uma função"