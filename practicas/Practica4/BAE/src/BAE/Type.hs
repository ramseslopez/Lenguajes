module Type where

    import qualified Data.List as List

    type Identifier = Int
    infix :->
        
    data Type = T Identifier
                | Integer | Boolean
                | Type :-> Type deriving (Eq, Show)

    type Substitution = [(Identifier, Type)]

    {- Función que devuelve las variables de tipo -}
    vars :: Type -> [Identifier]
    vars (T t)       = [t]
    vars (t1 :-> t2) = List.union (vars t1) (vars t2) 
    vars _           = [] 

    {- Función que aplica la sustitución a un tipo dado -}
    subst :: Type -> Substitution -> Type
    subst (T t) s       = case s of
            []              -> T t
            ((x, a) : ss)   -> if x == t then 
                                    a  
                                else 
                                    subst (T t) ss
    subst (t1 :-> t2) s = (subst t1 s) :-> (subst t2 s)

    {- Función que realiza la composición de dos sustituciones -}
    comp :: Substitution -> Substitution -> Substitution
    comp s1 s2 = List.union [(x, subst t s2) | (x, t) <- s1] [(x, t) | (x, t) <- s2, List.notElem x [y | (y, t) <- s1]]

    {- Función que elimina las sustituciones redundates -}
    simpl :: Substitution -> Substitution
    simpl [(x, s)] = if x == (getIndex s) then [] else [(x,s)]
    --simpl [(x, s1 :-> s2)] = if elem x (vars (s1 :-> s2)) then [] else [(x, s1 :-> s2)] 
    simpl ((x, s):ss) = if x == (getIndex s) then simpl ss else [(x, s)] ++ simpl ss  

    -- Función que obtiene el identificador de un tipo
    getIndex :: Type -> Int
    getIndex (T n) = n