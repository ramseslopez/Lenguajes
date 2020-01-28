module Bruijn where

    import Data.List
    import Data.Char

    type Identifier = String

    data ExprL = VL Identifier 
               | LL Identifier ExprL
               | AL ExprL ExprL deriving(Eq, Show)
               
    type Index = Int

    data ExprB = IB Index
               | LB ExprB
               | AB ExprB ExprB deriving(Eq, Show)

    type Substitution = (Index, ExprB)

    {- Función que se encarga de obtener el contexto canónico de una expresión -}
    ctx :: ExprL -> [Identifier]
    ctx e = case e of 
        VL x     -> [x]
        LL x e   -> ctx e \\ [x]
        AL e1 e2 -> (union (ctx e1) (ctx e2))

    {-  -}
    qn :: ([Identifier], ExprL) -> ExprB 
    qn (xs, e) = case e of
        VL x     -> IB 0
        LL x e   -> LB (qn (xs ++ [x], e))
        AL e1 e2 -> AB (qn (xs, e1)) (qn (xs, e2))
    
    
    newVar :: [Identifier] -> [Identifier]
    newVar xs = case xs of
        [] -> ["x"]
        (x:xs) -> 

    newVar' :: Identifier -> [Identifier] -> [Identifier]
    newVar' x xs
                | notElem x xs = x:xs
                | notElem (incrVar x) xs = (incrVar x): xs
                | otherwise = newVar' (incrVar x) xs


    {- Función que se encarga de incrementar variables en una unidad -}
    incrVar :: Identifier -> Identifier
    incrVar xs
                | isDigit(last xs) = (take ((length xs) - 1) xs) ++ show(intLast xs)
                | otherwise = xs ++ "1"
                where intLast :: String -> Int
                      intLast xs = read(take 1 (reverse xs)) + 1

