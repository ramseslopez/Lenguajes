module BAE.Type where

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
