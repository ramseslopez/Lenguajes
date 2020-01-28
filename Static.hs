module Static where
--
--    import Unifier
    import qualified Data.List as List
    import qualified Lambda
    import Unifier

    type Identifier = Int
    infix :->
        
    data Type = T Identifier
               | Type :-> Type deriving (Eq, Show)

    vars :: Type -> [Identifier]
    vars (T t)       = [t]
    vars (t1 :-> t2) = List.union (vars t1) (vars t2) 

    type Substitution = [(Identifier, Type)]

    subst :: Type -> Substitution -> Type
    subst (T t)       s = case s of
            []              -> T t
            ((x, a) : ss)   -> if x == t then 
                                    a  
                                else 
                                    subst (T t) ss
    subst (t1 :-> t2) s = (subst t1 s) :-> (subst t2 s)

    comp :: Substitution -> Substitution -> Substitution
    comp s1 s2 = [(x, subst t s2) | (x, t) <- s1] `List.union` [(x, t) | (x, t) <- s2, List.notElem x [y | (y, t) <- s1]]


    type Ctxt = [(Lambda.Identifier, Type)]


    substCtxt :: Ctxt -> Substitution -> Ctxt
    substCtxt [] _            = []
    substCtxt ((x, t) : cs) s = (x, subst t s) : substCtxt cs s

    find :: Lambda.Identifier -> Ctxt -> Maybe Type
    find _ [] = Nothing
    find x ((y, t) : cs) = if x == y then
                                Just t
                           else 
                                find x cs


    type Constraint = [(Type, Type)]


    fresh' :: Type -> [Type] -> Type 
    fresh' (T n) vars  = if List.elem (T n) vars then
                            fresh' (T (succ n)) vars 
                         else
                            (T n) 

    fresh :: [Type] -> Type
    fresh vars = fresh' (T 0) vars

    infer' :: ([Type], Lambda.Expr) -> ([Type], Ctxt, Type, Constraint)
    infer' (nv, (Lambda.V x)) = let t = fresh nv
                                    nv' = nv `List.union` [t]
                                in 
                                    (nv', [(x, t)],t, [])
    infer' (nv, (Lambda.L x e)) = let (nv', g, t, r) = infer' (nv, e)
                                  in 
                                    case find x g of
                                    Just t' -> (nv', g List.\\ [(x, t')], t' :-> t, r) 
                                    Nothing -> let t' = fresh nv' 
                                                   nv'' = nv' `List.union` [t']
                                                in (nv'', g, t' :-> t, r)
    infer' (nv, (Lambda.App e1 e2)) = let (nv1, g1, t1, r1) = infer' (nv, e1)
                                          (nv2, g2, t2, r2) = infer' (nv, e2)
                                          s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y]
                                          z = fresh nv2
                                          nv' = nv2 `List.union` [z]
                                      in 
                                        (nv', g1 `List.union` g2, z, r1 `List.union` r2 `List.union` s `List.union` [(t1, t2 :-> z)])
    
   {-} infer :: (Lambda.Expr) -> (Ctxt, Type)
    infer e = let (_, g, t, r) = infer' ([], e)
                  umg = µ r
              in 
                (substCtxt g umg, subst t umg)-}
     

    



    

    