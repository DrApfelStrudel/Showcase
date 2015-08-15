datatype lExp = ID of string | Lambda of string * lExp | Apply of lExp * lExp

fun lExpToString (ID s)           = s
  | lExpToString (Lambda (s, e))  = "λ"^s^"."^lExpToString(e)
  | lExpToString (Apply(ID s1, ID s2))   = s1^s2
  | lExpToString (Apply(ID s, e))        = s^"("^lExpToString(e)^")"
  | lExpToString (Apply(e, ID s))        = "("^lExpToString(e)^")"^s    
  | lExpToString (Apply (e1, e2)) = "("^lExpToString(e1)^")("^lExpToString(e2)^")"  
        
fun println s = print (s ^ "\r\n")

(* Generates a list of all unique nodes in the lambda expression *)
fun visitor e =
    let
        fun visit (node as (ID s)) = node :: nil
          | visit (node as Apply(e1, e2)) = node :: ((visit e1) @ (visit e2))
          | visit (node as Lambda(s,e)) = node :: (visit e) 

        fun removeDuplicates (e :: input') seen = if List.exists (fn x => x = e) seen
                                                  then removeDuplicates input' seen
                                                  else e :: (removeDuplicates input' (e :: seen))
          | removeDuplicates [] seen = []
    in
        removeDuplicates (visit e) []
    end
 
datatype constraintVariable = CVar of lExp

fun makeCVariables ((n :: ns') : lExp list) = (CVar n) :: (makeCVariables ns')
  | makeCVariables [] = [] 

fun cvar2string (CVar e) = "[["^lExpToString(e)^"]]"

datatype constraint = Sub of string * constraintVariable
                    | Imp of string * constraintVariable * constraintVariable * constraintVariable

fun c2string (Sub(s,cv)) = "{λ"^s^"} ⊆ "^cvar2string(cv)
  | c2string (Imp(s,c1,c2,c3)) = "λ"^s^" ∈ "^cvar2string(c1)^" ⇒ "^cvar2string(c2)^" ⊆ "^cvar2string(c3)

fun findLambdas ((n as Lambda(_,_)) :: rest') = n :: (findLambdas rest')
  | findLambdas (r :: rest') = findLambdas rest'  
  | findLambdas [] = nil

fun generateConstraints e =
    let
        val nodes = visitor e
        val lambdas = findLambdas nodes
     
        fun genA (Apply(e1,e2)) (Lambda(s,e) :: rest') = Imp(s, CVar(e1), CVar(e2), CVar(ID s)) ::
                                                         Imp(s, CVar(e1), CVar(e), CVar(Apply(e1,e2))) ::
                                                         genA (Apply(e1,e2)) rest'
          | genA _ _ = []

        fun gen ((n as Lambda(s,e)) :: rest') = Sub(s, CVar(n)) :: (gen rest')
          | gen ((n as Apply(e1,e2)) :: rest') = (genA n lambdas) @ (gen rest')  
          | gen (n :: rest') = gen rest'
          | gen [] = []  
    in
        gen nodes
    end

fun printConstraints [] = ()
  | printConstraints (c :: cs') = (println (c2string c); printConstraints cs') 

val test1 = Lambda("x", Apply(ID("x"), ID("x")))
val test2 = Apply(Lambda("f", Apply( Apply(ID("f"), ID("f")), Lambda("y", ID("y")))),
                  Lambda("x", ID("x")))
val test3 = Apply(test1, Lambda("y", Lambda("z", Apply(ID("y"), ID("z")))))
