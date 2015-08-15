type graph = int * ((int * int) list)

exception malformed_string of string

fun checkBitString (bitString : string) =
    let
        val bitList = explode bitString

        fun checkBitList [] = ()
          | checkBitList (#"0" :: bits') = checkBitList bits'
          | checkBitList (#"1" :: bits') = checkBitList bits'
          | checkBitList _ = raise malformed_string ("'"^bitString^"' is not a bitString!")
    in
        checkBitList bitList
    end

fun findSquare n =
    let
        fun aux c n = if c * c > n then NONE else
                      if c * c = n then SOME c else
                      aux (c + 1) n
    in
        aux 1 n
    end

fun bits2Graph (bitString : string) =
    let
        val _ = checkBitString bitString

        val vertexCount = case findSquare (size bitString) 
                           of NONE => raise malformed_string("Not a proper graph")
                            | SOME n => n 

        fun parser row col (#"0" :: bits') = if col = vertexCount then parser (row+1) 1 bits' else parser row (col+1) bits'
          | parser row col (#"1" :: bits') = if col = vertexCount then (row, col) :: parser (row+1) 1 bits' else (row, col) :: parser row (col+1) bits'
          | parser row col [] = []  
          | parser _ _ _ = [] (* Should not happen *) 
    in
        (vertexCount, parser 1 1 (explode bitString))
    end

fun graph2Dot ((vertexCount, edges) : graph) =
    let
        fun makeVertices 0 : string = ""
          | makeVertices n : string = "    Node"^Int.toString(n)^"\r\n"^(makeVertices(n-1))

        fun makeEdges ((i,j) :: edges') = "    Node"^Int.toString(i)^" -> "^"Node"^Int.toString(j)^"\r\n"^(makeEdges edges')
          | makeEdges [] = "" 
    in
       "digraph G {\r\n" ^ (makeVertices vertexCount) ^ (makeEdges edges) ^ "}\r\n" 
    end

fun bitGraph2Dot (bitString : string) = graph2Dot (bits2Graph bitString)

