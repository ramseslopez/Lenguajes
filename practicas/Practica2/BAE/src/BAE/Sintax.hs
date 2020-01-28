module BAE.Sintax where

  import Data.List

  data Expr = V Identifier | I Int | B Bool
              | Add Expr Expr | Mul Expr Expr | Succ Expr | Pred Expr
              | Not Expr | And Expr Expr | Or Expr Expr
              | Lt Expr Expr | Gt Expr Expr | Eq Expr Expr
              | If Expr Expr Expr
              | Let Identifier Expr Expr deriving (Eq)

  type Identifier = String

  instance Show Expr where
    show e = case e of
      (V x)       -> "V[" ++ x ++ "]"
      (I n)       -> "N[" ++ (show n) ++ "]"
      (B t)       -> "B[" ++ (show t) ++ "]"
      (Add a b)   -> "add(" ++ (show a) ++ ", " ++ (show b) ++ ")"
      (Mul a b)   -> "mul(" ++ (show a) ++ ", " ++ (show b) ++ ")"
      (Succ a)    -> "succ(" ++ (show a) ++ ")"
      (Pred a)    -> "pred(" ++ (show a) ++ ")"
      (Not a)     -> "not(" ++ (show a) ++ ")"
      (And a b)   -> "and(" ++ (show a) ++ ", " ++ (show b) ++ ")"
      (Or a b)    -> "or(" ++ (show a) ++ ", " ++ (show b) ++ ")"
      (Lt a b)    -> "lt(" ++ (show a) ++ ", " ++ (show b) ++ ")"
      (Gt a b)    -> "gt(" ++ (show a) ++ ", " ++ (show b) ++ ")"
      (Eq a b)    -> "eq(" ++ (show a) ++ ", " ++ (show b) ++ ")"
      (If a b c)  -> "if(" ++ (show a) ++ ", " ++ (show b) ++ ", " ++ (show c) ++ ")"
      (Let x a b) -> "let(" ++ (show a) ++ ", " ++ x ++ "." ++ (show b) ++ ")"

  type Substitution = (Identifier, Expr)

  -- Función que devuelve las variables libres de una expresión
  frVars :: Expr -> [Identifier]
  frVars (I n)       = []
  frVars (B t)       = []
  frVars (V x)       = [x]
  frVars (Add a b)   = eliminaR ((frVars a) ++ (frVars b))
  frVars (Mul a b)   = eliminaR ((frVars a) ++ (frVars b))
  frVars (Succ a)    = frVars a
  frVars (Pred a)    = frVars a
  frVars (Not a)     = frVars a
  frVars (And a b)   = eliminaR ((frVars a) ++ (frVars b))
  frVars (Or a b)    = eliminaR ((frVars a) ++ (frVars b))
  frVars (Lt a b)    = eliminaR ((frVars a) ++ (frVars b))
  frVars (Gt a b)    = eliminaR ((frVars a) ++ (frVars b))
  frVars (Eq a b)    = eliminaR ((frVars a) ++ (frVars b))
  frVars (If a b c)  = eliminaR ((frVars a) ++ (frVars b) ++ (frVars c))
  frVars (Let x a b)
                    | elem x (frVars b) = eliminaR ((frVars a) ++ ((frVars b) \\ [x]))
                    | otherwise = eliminaR ((frVars a) ++ (frVars b))

  -- Función que se encarga de eliminar elementos repetidos en una lista
  eliminaR :: (Eq a) => [a] -> [a]
  eliminaR [] = []
  eliminaR (x:xs)
                  | elem x xs = eliminaR xs
                  | otherwise = [x] ++ eliminaR xs

  -- Función encargada de realizar una sustitución a una expresión
  -- en caso de ser posible
  subst ::  Expr -> Substitution -> Expr
  subst (I n) (a, b)       = (I n)
  subst (B t) (a, b)       = (B t)
  subst (V x) (a, b)
                          | x == a = b
                          | otherwise = (V x)
  subst (Add n m) (a, b)   = Add (subst n (a,b)) (subst m (a,b))
  subst (Mul n m) (a, b)   = Mul (subst n (a,b)) (subst m (a,b))
  subst (Succ n) (a, b)    = Succ (subst n (a, b))
  subst (Pred n) (a, b)    = Pred (subst n (a,b))
  subst (Not p) (a, b)     = Not (subst p (a, b))
  subst (And p q) (a, b)   = And (subst p (a,b)) (subst q (a,b))
  subst (Or p q) (a, b)    = Or (subst p (a,b)) (subst q (a,b))
  subst (Lt n m) (a,b)     = Lt (subst n (a,b)) (subst m (a,b))
  subst (Gt n m) (a, b)    = Gt (subst n (a,b)) (subst m (a,b))
  subst (Eq n m) (a, b)    = Eq (subst n (a,b)) (subst m (a,b))
  subst (If e f h) (a, b)  = If (subst e (a, b)) (subst f (a, b)) (subst h (a, b))
  subst (Let x a b) (c, d) = let t
                                  | notElem x ([c] ++ (frVars d)) = subst b (c, d)
                                  | otherwise = error "La sustitucion no puede ser realizada"
                              in Let x (subst a (c, d)) t
{-if (x==y) then
  (Let x (susbst a (c,d)) b)
  else if (elem x (frVars es)) then
    error ":("
    else
      (Let x (susbs a (a (c, d)) (subst b (c,d)))) 
-}

  -- Función que se encarga de verificar si dos expresiones son
  -- alpha-equivalentes
  alphaEq :: Expr -> Expr -> Bool
  alphaEq (I n) (I m)
                                  | n == m = True
                                  | otherwise = False
  alphaEq (B t) (B f)
                                  | t == f = True
                                  | otherwise = False
  alphaEq (V x) (V y)             = True
  alphaEq (Add n m) (Add n1 m1)   = (alphaEq n n1) && (alphaEq m m1)
  alphaEq (Mul n m) (Mul n1 m1)   = (alphaEq n n1) && (alphaEq m m1)
  alphaEq (Succ n) (Succ m)       = alphaEq n m
  alphaEq (Pred n) (Pred m)       = alphaEq n m
  alphaEq (Not p) (Not q)         = alphaEq p q
  alphaEq (And p q) (And s t)     = (alphaEq p s) && (alphaEq q t)
  alphaEq (Or p q) (Or s t)       = (alphaEq p s) && (alphaEq q t)
  alphaEq (Lt n m) (Lt n1 m1)     = (alphaEq n n1) && (alphaEq m m1) 
  alphaEq (Gt n m) (Gt n1 m1)     = (alphaEq n n1) && (alphaEq m m1)
  alphaEq (Eq n m) (Eq n1 m1)     = (alphaEq n n1) && (alphaEq m m1)
  alphaEq (If a b c) (If d e f)   = (alphaEq a d) && (alphaEq b e) && (alphaEq c f)
  alphaEq (Let x a b) (Let y c d) = alphaEq l s
                                    where l = subst b (x,a)
                                          s = subst d (y, a)
  -- alphaEq (Let x a b) (Let y c d) = (alphaEq a c) && (alphaEq d (subst b (x, V y)))                                          
  alphaEq _ _ = False
