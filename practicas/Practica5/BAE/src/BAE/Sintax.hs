module BAE.Sintax where

  import Data.List
  import Data.Char

  data Expr = V Identifier | I Int | B Bool
              | Add Expr Expr | Mul Expr Expr | Succ Expr | Pred Expr
              | Not Expr | And Expr Expr | Or Expr Expr
              | Lt Expr Expr | Gt Expr Expr | Eq Expr Expr
              | If Expr Expr Expr
              | Let Identifier Expr Expr
              | Fn Identifier Expr
              | App Expr Expr 
              | L Int | Alloc Expr | Deref Expr | Assig Expr Expr
              | Void | Seq Expr Expr | While Expr Expr deriving (Eq)

  type Identifier = String

  instance Show Expr where
    show e = case e of
      (V x)         -> "V[" ++ x ++ "]"
      (I n)         -> "N[" ++ (show n) ++ "]"
      (B t)         -> "B[" ++ (show t) ++ "]"
      (Add e1 e2)   -> "add(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      (Mul e1 e2)   -> "mul(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      (Succ e)      -> "succ(" ++ (show e) ++ ")"
      (Pred e)      -> "pred(" ++ (show e) ++ ")"
      (Not e)       -> "not(" ++ (show e) ++ ")"
      (And e1 e2)   -> "and(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      (Or e1 e2)    -> "or(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      (Lt e1 e2)    -> "lt(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      (Gt e1 e2)    -> "gt(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      (Eq e1 e2)    -> "eq(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      (If e1 e2 e3) -> "if(" ++ (show e1) ++ ", " ++ (show e2) ++ ", " ++ (show e3) ++ ")"
      (Let x e1 e2) -> "let(" ++ (show e1) ++ ", " ++ x ++ "." ++ (show e2) ++ ")"
      (Fn x e)      -> "fn(" ++ x ++ "." ++ (show e) ++ ")"
      (App e1 e2)   -> "app(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      (L n)         -> "l => " ++ (show n) 
      (Alloc e)     -> "alloc" ++ (show e) ++ ")"
      (Void)        -> "void"
      (Assig e1 e2) -> (show e1) ++ " ::= " ++ (show e2)
      (Deref e)     -> "!" ++ (show e)
      (Seq e1 e2)   -> (show e1) ++ ";" ++ (show e2)
      (While e1 e2) -> "while " ++ (show e1) ++ " do " ++ (show e2)
 

  type Substitution = (Identifier, Expr)

  {- Función que devuelve las variables libre de una expresión -}
  frVars :: Expr -> [Identifier]
  frVars e = case e of
          I n         -> []
          B t         -> []
          V x         -> [x]
          L n         -> []
          Void        -> []
          Succ e      -> frVars e
          Pred e      -> frVars e
          Add e1 e2   -> union (frVars e1) (frVars e2)
          Mul e1 e2   -> union (frVars e1) (frVars e2)
          Not e       -> frVars e
          And e1 e2   -> union (frVars e1) (frVars e2)
          Or e1 e2    -> union (frVars e1) (frVars e2)
          Lt e1 e2    -> union (frVars e1) (frVars e2)
          Eq e1 e2    -> union (frVars e1) (frVars e2)
          Gt e1 e2    -> union (frVars e1) (frVars e2)
          If e1 e2 e3 -> union (frVars e1)  (union (frVars e2) (frVars e3))
          Let x e1 e2 -> if elem x (frVars e2) 
                          then 
                            union (frVars e1) (frVars e2 \\ [x]) 
                          else 
                            union (frVars e1) (frVars e2)
          Fn x e      -> if elem x (frVars e) 
                          then 
                            (frVars e \\ [x]) 
                          else 
                            frVars e
          App e1 e2   -> union (frVars e1) (frVars e2)
          Alloc e     -> frVars e
          Deref e     -> frVars e
          Assig e1 e2 -> union (frVars e1) (frVars e2)
          Seq e1 e2   -> union (frVars e1) (frVars e2)
          While e1 e2 -> union (frVars e1) (frVars e2)

  subst :: Expr -> Substitution -> Expr
  subst e s@(y, a) = case e of
          I n         -> I n
          B t         -> B t
          V x         -> if x == y then a else V x
          L n         -> L n
          Void        -> Void 
          Succ e      -> Succ (subst e s)
          Pred e      -> Pred (subst e s)
          Add e1 e2   -> Add (subst e1 s) (subst e2 s)
          Mul e1 e2   -> Mul (subst e1 s) (subst e2 s)
          Not e       -> Not (subst e s)
          And e1 e2   -> And (subst e1 s) (subst e2 s)
          Or e1 e2    -> Or (subst e1 s) (subst e2 s)
          Lt e1 e2    -> Lt (subst e1 s) (subst e2 s)
          Gt e1 e2    -> Gt (subst e1 s) (subst e2 s)
          Eq e1 e2    -> Eq (subst e1 s) (subst e2 s)
          If e1 e2 e3 -> If (subst e1 s) (subst e2 s) (subst e3 s)
          Let x e1 e2 -> Let x (subst e1 s) t 
                          where t = if notElem x ([y] ++ (frVars a)) 
                                    then 
                                      subst e2 s 
                                    else 
                                      error "La sustitucion no puede ser realizada"
          Fn x e      -> if elem x (frVars a) 
                          then 
                            Fn (incrVar x) (subst e s) 
                          else 
                            Fn x (subst e s)
          App e1 e2   -> App (subst e1 s) (subst e2 s)
          Alloc e     -> Alloc (subst e s)
          Deref e     -> Deref (subst e s)
          Assig e1 e2 -> Assig (subst e1 s) (subst e2 s)
          Seq e1 e2   -> Seq (subst e1 s) (subst e2 s)
          While e1 e2 -> While (subst e1 s) (subst e2 s)



  -- Funciones auxiliares --

  {- Función que se encarga de incrementar variables en una unidad -}
  incrVar :: Identifier -> Identifier
  incrVar xs
              | isDigit(last xs) = (take ((length xs) - 1) xs) ++ show(intLast xs)
              | otherwise        = xs ++ "1"

  {- Función que se encarga de sumar 1 al último elemento de uan lista de números -}
  intLast :: String -> Int
  intLast xs = read(take 1 (reverse xs)) + 1
