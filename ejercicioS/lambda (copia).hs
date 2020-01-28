module Lambda where

    import Data.List
    import Data.Char

    -- Sintaxis

    data Expr = V Identifier 
                | L Identifier Expr
                | App Expr Expr deriving(Eq)

    type Identifier = String

    instance Show Expr where
        show e = case e of
            (V x) -> x
            (L x e) -> "\\" ++ x ++ "-> " ++ (show e)
            (App e1 e2) -> "(" ++ (show e1) ++ " " ++ (show e2) ++ ")" 

    -- Sustitución ..

    type Substitution = (Identifier, Expr)

    {- Función que obtiene las variables libres de una expresión -}
    frVars :: Expr -> [Identifier]
    frVars (V x) = [x]
    frVars (L x e) 
                | elem x (frVars e) = (frVars e \\ [x]) 
                | otherwise =  frVars e
    frVars (App e1 e2) = union (frVars e1) (frVars e2) 

    {- Función que se encarga de incrementar variables en una unidad -}
    incrVar :: Identifier -> Identifier
    incrVar xs
                | isDigit(last xs) = (take ((length xs) - 1) xs) ++ show(intLast xs)
                | otherwise = xs ++ "1"


    {- Función que se encarga de devolver una expresión equivalente -}
    alphaExpr :: Expr -> Expr
    alphaExpr (V x) = V (incrVar x)
    alphaExpr (L x (L y e)) = (L (incrVar x) (alphaExpr (L y e)))
    alphaExpr (L x e)
                    | elem x (frVars e) = (L (incrVar x) (alphaExpr e))  
                    | otherwise = (L x e)
    alphaExpr (App e1 e2) = App (alphaExpr e1) (alphaExpr e2)
    alphaExpr _ = error "No se puede procesar"

    {- Función que se encarga de realizar una sustitución dada -}
    subst :: Expr -> Substitution -> Expr
    subst (V x) (y, e) 
                    | x == y = e 
                    | otherwise = (V x)
    subst (L x e1) (y, e)
                    | elem x (frVars e) = L (incrVar x) (subst e1 (y, e))
                    | elem y (frVars e1) = L x (subst e1 (y, e)) 
                    | otherwise = (L x e1)
    subst (App e1 e2) (y, e) = App (subst e1 (y, e)) (subst e2 (y, e))
    subst _ _ = error "No se puede procesar"

    
    -- Beta-reducción --
    
    {- Función que se encarga de implementar una beta reducción -}
    beta :: Expr -> Expr
    beta (V x) = (V x)
    beta (L x e) = L x (beta e)
    beta (App (L x e) e2) = subst e (x, e2)
    beta _ = error "No se p1|uede procesar la operacion"

    {- Función que determina si una expresión es normal -}
    normal :: Expr -> Bool
    normal (V x) = True 
    normal (L x e) = (normal e)                              
    normal (App e1 e2) = (normal e1) && (normal e2) && (exprL e1) 
    normal _ = False   

    {- Función que se encarga de evaluar una expresión lambda -}
    eval :: Expr -> Expr
    eval (V x) = V x
    eval (L x e) = L x (eval e)
    eval (App e1 e2) = App (eval e1) (eval e2)

    -- Funciones auxiliares --

    {- Función que se encarga de sumar 1 al último elemento de uan lista de números -}
    intLast :: String -> Int
    intLast xs = read(take 1 (reverse xs)) + 1

    {- Función que verifica si una expresión es una expresión Lambda -}
    exprL :: Expr -> Bool
    exprL (V x) = True
    exprL (L x e) = False
    exprL (App e1 e2) = (exprL e1) || (exprL e2) 