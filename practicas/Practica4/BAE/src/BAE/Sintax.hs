module Sintax where

  import Data.List
  import Data.Char

  data Expr = V Identifier | I Int | B Bool
              | Add Expr Expr | Mul Expr Expr | Succ Expr | Pred Expr
              | Not Expr | And Expr Expr | Or Expr Expr
              | Lt Expr Expr | Gt Expr Expr | Eq Expr Expr
              | If Expr Expr Expr
              | Let Identifier Expr Expr
              | Fn Identifier Expr
              | App Expr Expr deriving (Eq)

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


  type Substitution = (Identifier, Expr)

  -- Función que devuelve las variables libres de una expresión
  frVars :: Expr -> [Identifier]
  frVars (I n)         = []
  frVars (B t)         = []
  frVars (V x)         = [x]
  frVars (Add e1 e2)   = union (frVars e1) (frVars e2)
  frVars (Mul e1 e2)   = union (frVars e1) (frVars e2)
  frVars (Succ e)      = frVars e
  frVars (Pred e)      = frVars e
  frVars (Not e)       = frVars e
  frVars (And e1 e2)   = union (frVars e1) (frVars e2)
  frVars (Or e1 e2)    = union (frVars e1) (frVars e2)
  frVars (Lt e1 e2)    = union (frVars e1) (frVars e2)
  frVars (Gt e1 e2)    = union (frVars e1) (frVars e2)
  frVars (Eq e1 e2)    = union (frVars e1) (frVars e2)
  frVars (If e1 e2 c)  = union (frVars e1)  (union (frVars e2) (frVars c))
  frVars (Let x e1 e2)
      | elem x (frVars e2) = union (frVars e1) (frVars e2 \\ [x])
      | otherwise = union (frVars e1) (frVars e2)
  frVars (Fn x e)
      | elem x (frVars e) = (frVars e \\ [x])
      | otherwise = frVars e
  frVars (App e1 e2)   = union (frVars e1) (frVars e2)

  {- Función que se encarga de incrementar variables en una unidad -}
  incrVar :: Identifier -> Identifier
  incrVar xs
              | isDigit(last xs) = (take ((length xs) - 1) xs) ++ show(intLast xs)
              | otherwise        = xs ++ "1"

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
  subst (Fn x e) (c, d)
                          | elem x (frVars d) = Fn (incrVar x) (subst e (c, d))
                          | otherwise = Fn x (subst e (c, d))
  subst (App e1 e2) (c, d) = App (subst e1 (c, d)) (subst e2 (c, d))
  subst _ _ = error "La sustitución no puede ser realizada"

  -- Función que se encarga de verificar si dos expresiones son
  -- alpha-equivalentes
  alphaExpr :: Expr -> Expr
  alphaExpr (I n)         = (I n)
  alphaExpr (B b)         = (B b)
  alphaExpr (V x)         = V (incrVar x)
  alphaExpr (Add e1 e2)   = Add (alphaExpr e1) (alphaExpr e2)
  alphaExpr (Mul e1 e2)   = Mul (alphaExpr e1) (alphaExpr e2)
  alphaExpr (Succ e)      = Succ (alphaExpr e)
  alphaExpr (Pred e)      = Pred (alphaExpr e)
  alphaExpr (Not e)       = Not (alphaExpr e)
  alphaExpr (And e1 e2)   = And (alphaExpr e1) (alphaExpr e2)
  alphaExpr (Or e1 e2)    = Or (alphaExpr e1) (alphaExpr e2)
  alphaExpr (Lt e1 e2)    = Lt (alphaExpr e1) (alphaExpr e2)
  alphaExpr (Gt e1 e2)    = Gt (alphaExpr e1) (alphaExpr e2)
  alphaExpr (Eq e1 e2)    = Eq (alphaExpr e1) (alphaExpr e2)
  alphaExpr (If e1 e2 e3) = If (alphaExpr e1) (alphaExpr e2) (alphaExpr e3)
  alphaExpr (Let x e1 e2) = Let (incrVar x) (alphaExpr e1) (alphaExpr e2)
  alphaExpr (Fn x e)      = Fn (incrVar x) (alphaExpr e)
  alphaExpr (App e1 e2)   = App (alphaExpr e1) (alphaExpr e2)
  alphaExpr _             = error "La expresión no existe"
 
  {- Función que decide si dos expresiones son alpha-equivalentes -}
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
  alphaEq (Fn x e1) (Fn y e2)     = (alphaEq e1 e2)
  alphaEq (App e1 e2) (App d1 d2) = (alphaEq e1 d1) && (alphaEq e2 d2)                                          
  alphaEq _ _ = False


  -- Funciones auxiliares --

  {- Función que se encarga de sumar 1 al último elemento de uan lista de números -}
  intLast :: String -> Int
  intLast xs = read(take 1 (reverse xs)) + 1
