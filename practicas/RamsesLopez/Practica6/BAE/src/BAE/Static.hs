module BAE.Static where

    import qualified Data.List as List
    import qualified BAE.Type as Type
    import qualified BAE.Sintax as Sintax
    import BAE.Unifier
    
    type Constraint = [(Type.Type, Type.Type)]

    type Ctxt = [(Sintax.Identifier, Type.Type)]

    {- Función que aplica una sustitución a un contexto dado -}
    subst :: Ctxt -> Type.Substitution -> Ctxt
    subst [] _            = []
    subst ((x, t) : cs) s = (x, Type.subst t s) : subst cs s

    {- Función que busca el tipo de una variable en un contexto dado -}
    find :: Sintax.Identifier -> Ctxt -> Maybe Type.Type
    find _ [] = Nothing
    find x ((y, t) : cs) = if x == y then
                                Just t
                           else 
                                find x cs

    {- Función que obtien4 una variable fresca -}
    fresh' :: Type.Type -> [Type.Type] -> Type.Type 
    fresh' (Type.T n) v  = if List.elem (Type.T n) v then
                            fresh' (Type.T (succ n)) v 
                         else
                            (Type.T n) 

    fresh :: [Type.Type] -> Type.Type
    fresh v = fresh' (Type.T 0) v

    {- Función que infiere el tipo de una expresión -}
    infer' :: ([Type.Type], Sintax.Expr) -> ([Type.Type], Ctxt, Type.Type, Constraint)
    infer' (v, (Sintax.I _)) = (v, [], Type.Integer, [])
    infer' (v, (Sintax.B _)) = (v, [], Type.Boolean, [])
    infer' (v, (Sintax.V x)) = let t = fresh v  
                                   v' = List.union v [t]
                               in
                                  (v', [(x, t)], t, [])
    infer' (v, (Sintax.Add e1 e2)) = let (v1, g1, t1, c1) = infer' (v, e1)
                                         (v2, g2, t2, c2) = infer' (v, e2)
                                         s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y]
                                         z = fresh v2
                                         v' = List.union v2 [z]
                                     in
                                      (v', List.union g1 g2, z, c1 `List.union` c2 `List.union` s `List.union` [(t1, t2 Type.:-> z)])
    infer' (v, (Sintax.Mul e1 e2)) = let (v1, g1, t1, c1) = infer' (v, e1)
                                         (v2, g2, t2, c2) = infer' (v, e2)
                                         s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y]
                                         z = fresh v2
                                         v' = List.union v2 [z]
                                     in
                                      (v', List.union g1 g2, z, c1 `List.union` c2 `List.union` s `List.union` [(t1, t2 Type.:-> z)])
    infer' (v, (Sintax.Succ e)) = let (v1, g1, t1, c1) = infer' (v, e) in (v, g1, Type.Integer, (t1, Type.Integer):c1)
    infer' (v, (Sintax.Pred e)) = let (v, g1, t1, c1) = infer' (v, e) in (v, g1, Type.Integer, (t1, Type.Integer):c1)
    infer' (v, (Sintax.Not e)) = let (v, g1, t1, c1) = infer' (v, e) in (v, g1, Type.Boolean, (t1, Type.Boolean):c1)
    infer' (v, (Sintax.And e1 e2)) = let (v1, g1, t1, c1) = infer' (v, e1)
                                         (v2, g2, t2, c2) = infer' (v, e2)
                                         s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y]
                                         z = fresh v2
                                         v' = List.union v2 [z]
                                     in
                                      (v', List.union g1 g2, z, c1 `List.union` c2 `List.union` s `List.union` [(t1, t2 Type.:-> z)])
    infer' (v, (Sintax.Or e1 e2)) = let (v1, g1, t1, c1) = infer' (v, e1)
                                        (v2, g2, t2, c2) = infer' (v, e2)
                                        s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y]
                                        z = fresh v2
                                        v' = List.union v2 [z]
                                     in
                                      (v', List.union g1 g2, z, c1 `List.union` c2 `List.union` s `List.union` [(t1, t2 Type.:-> z)])
    infer' (v, (Sintax.Lt e1 e2)) = let (v1, g1, t1, c1) = infer' (v, e1)
                                        (v2, g2, t2, c2) = infer' (v, e2)
                                        s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y]
                                        z = fresh v2
                                        v' = List.union v2 [z]
                                     in
                                      (v', List.union g1 g2, z, c1 `List.union` c2 `List.union` s `List.union` [(t1, t2 Type.:-> z)])
    infer' (v, (Sintax.Gt e1 e2)) = let (v1, g1, t1, c1) = infer' (v, e1)
                                        (v2, g2, t2, c2) = infer' (v, e2)
                                        s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y]
                                        z = fresh v2
                                        v' = List.union v2 [z]
                                     in
                                      (v', List.union g1 g2, z, c1 `List.union` c2 `List.union` s `List.union` [(t1, t2 Type.:-> z)])
    infer' (v, (Sintax.Eq e1 e2)) = let (v1, g1, t1, c1) = infer' (v, e1)
                                        (v2, g2, t2, c2) = infer' (v, e2)
                                        s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y]
                                        z = fresh v2
                                        v' = List.union v2 [z]
                                     in
                                      (v', List.union g1 g2, z, c1 `List.union` c2 `List.union` s `List.union` [(t1, t2 Type.:-> z)])
    infer' (v, (Sintax.If e1 e2 e3)) = error "Falta implementar"
    infer' (v, (Sintax.Let x e1 e2)) = error "Falta implementar"
    infer' (v, (Sintax.Fn x e)) = let (v', g1, t1, c1) = infer' (v, e) in case find x g1 of
        Just t1' -> (v', filter (\(i, t1) -> i /= x) g1, t1' Type.:-> t1, c1)
        Nothing -> let t1' = fresh v'; v'' = v' `List.union` [t1'] in (v'', g1, t1' Type.:-> t1, c1)
    infer' (v, (Sintax.App e1 e2)) = let (v1, g1, t1, c1) = infer' (v, e1)
                                         (v2, g2, t2, c2) = infer' (v, e2)
                                         s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y]
                                         z = fresh v2
                                         v' = List.union v2 [z]
                                     in
                                      (v', List.union g1 g2, z, c1 `List.union` c2 `List.union` s `List.union` [(t1, t2 Type.:-> z)])
    
    -- Función que infiere el tipo válido en un contexto dado -
  --  infer :: Sintax.Expr -> (Ctxt, Type.Type)
    --infer e = let (_, g, t, r) = infer' ([], e)
        --          umg = µ r
      --        in 
          --      (subst g umg, subst t umg)