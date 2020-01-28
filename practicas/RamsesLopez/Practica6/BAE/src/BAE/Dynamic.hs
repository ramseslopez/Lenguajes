    module BAE.Dynamic where

        import BAE.Sintax

        {- Función que dada una memoria y una expresión, devuelve la reducción en un paso -}
        eval1 :: State -> State
        eval1 (E  (me,s,e)) = case e of
            V _ -> R (me,s, e)
            I _ -> R (me,s, e)
            B _ -> R (me,s ,e)
            Fn x e -> (E (me,(FnT x ():s), e))
            Succ e -> E (me,(SuccF (): s), e)
            Pred e -> E (me,(PredF (): s), e)
            Add e1 e2 -> E (me,(AddFL () e2 : s), e1)
            Mul e1 e2 -> E (me,(MulFL () e2 : s), e1)
            Not e1 -> E (me,(NotF (): s), e1)
            And e1 e2 -> E (me,(AndFL () e2 : s), e1)
            Or e1 e2 -> E (me,(OrFL () e2 : s), e1)
            Gt e1 e2 -> E (me,(GtFL () e2 : s), e1)
            Lt e1 e2 -> E (me,(LtFL () e2 : s), e1)
            Eq e1 e2 -> E (me,(EqFL () e2 : s), e1)
            App e1 e2 -> E (me,(AppFL () e2 : s), e1)
            If e1 e2 e3 -> E (me,(IfT () e2 e3 : s), e1)
            Let x e1 e2 -> E (me,(LetT x () e2:s), e1)
            L n -> R (me ++ [(n, Void)], s, Void)
            Alloc e -> E (me ,(AllocF () : s), e)
            Deref e -> E (me, (DerefF (): s), e)
            Assig e1 e2 -> E (me, (AssigFL () e2 : s), e1)
            Void -> R (me, s, Void)
            While e1 e2 -> (E (me, (WhileFL () e2 : s), e1))
            Raise e -> E (me, (RaiseF () : s), e)
            Handle e1 x e2 -> E (me, ((HandleF () x e2) : s), e1)
            Handle (Raise e1) x e2 -> E (me, ((HandleF () x e2) : s), Raise e1)
            LetCC x e -> E (me, (LetCCF x () : s), e)
        eval1 (R (me, s, e)) = case e of
            (V x) -> case s of
                (LetT x _ e2 : s') -> E (me, s', subst' e2 (x, e))
            I m ->  case s of
                ((FnT x _) : s') -> R (me,s', Fn x e)
                ((SuccF _) : s') -> R (me, s', I (m + 1))
                ((PredF _) : s') -> R (me,s', I (m - 1))
                ((AddFL _ e2) : s') -> E (me, (AddFR e () : s'), e2)
                ((AddFR (I n) _) : s' ) -> R (me, s', I (n + m))
                ((MulFL _ e2) : s') -> E (me, (MulFR e () : s'), e2)
                ((MulFR (I n) _) : s') -> R (me, s', I (n * m))
                ((LtFL _ e2) : s') -> E (me, (LtFR e () : s'), e2)
                ((LtFR (I n) _) : s') ->  R (me, s', B (n < m))
                ((GtFL _ e2) : s') -> E (me, (GtFR e () : s'), e2)
                ((GtFR (I n) _) : s') -> R (me, s', B (n > m))
                ((EqFL _ e2) : s') -> E (me, (EqFR e () : s'), e2)
                ((EqFR (I n) _) : s') -> R (me, s', B (n == m))
                ((LetT x _ e2) : s') -> E (me, s', subst' e2 (x, e))
                ((RaiseF _) : s') -> P (me, s', Raise (I m))
                ((HandleF _ x e1) : s' ) -> P (me, s', I m)
                ((HandleF _ x e1) : s') -> P (me, s', Raise (I m))
                ((HandleF _ x e1) : s') -> P (me, s', subst' e1 (x, (I m)))
                ((AllocF _ ) :s') -> R (me ++ [(0,e)],s', Void)
                ((DerefF _ ) :s') -> R (me, s',(getExpr me m))
                ((LetCCF x _) :s') -> R (me, s', (subst' e (x, (Cont s'))))
                ((ContinueFL _ e2) : s') -> E (me, (ContinueFR e () : s'), e2)
                ((ContinueFR (I n) _) : s') -> R (me, s', e)
            B q -> case s of
                ((FnT x _):s') -> R (me, s', Fn x e)
                ((NotF _):s') -> R (me, s', Not e)
                ((AndFL _ e2) : s') -> E (me, (AndFR e () : s'), e2)
                ((AndFR (B p) _) : s') -> R (me, s', B (p && q))
                ((OrFL _ e2) : s') -> E (me,(OrFR e () : s'), e2)
                ((OrFR (B n) _) : s') -> R (me,s', B (n || q))
                ((IfT _ e2 e3):s') -> E (me,s', if q then e2 else e3)
                ((LetT x _ e2): s') ->  E (me, s', subst' e2 (x, e))
                ((WhileFL _ e2): s') -> E (me, (WhileFR e () : s'), e2)
                ((WhileFR a _) : s') -> case a of
                  (B True) -> E (me, s', If (B True) (Seq a (While a e)) Void)
                  (B False) -> E(me, s', Void)
                ((AllocF _ ) :s') -> R (me ++ [(0,e)],s', Void)
                ((RaiseF _) : s') -> P (me, s', Raise (B q))
                ((HandleF _ x e1) : s' ) -> P (me, s', B q)
                ((HandleF _ x e1) : s') -> P (me, s', Raise (B q))
                ((LetCCF x _) :s') -> R (me, s', (subst' e (x, (Cont s'))))
                ((ContinueFL _ e2) : s') -> E (me, (ContinueFR e () : s'), e2)
                ((ContinueFR (B p) _) : s') -> R (me, s', e)



    	evals :: State -> State
    	evals (E (me,[], e))
    		| (evalsAuxk e) = (E (me,[], e))
    		| otherwise = evals (eval1 (E  (me,[], e)))
    	evals (E (me,s, e)) = evals (eval1 (E  (me,s, e)))
    	evals (R (me,[], e))
    		| (evalsAuxk e) = (R (me,[], e))
    		| otherwise = evals (eval1 (R (me,[], e)))
    	evals (R (me,s, e)) = evals (eval1 (R (me,s, e)))
    	evals (P (me,[], e))
    		| (evalsAuxk e) = (P (me,[], e))
    		| otherwise = evals (eval1 (P (me,[], e)))
    	evals (P (me,s, e)) = evals (eval1 (P (me,s, e)))

    	evaleAuxNo :: State -> Expr
    	evaleAuxNo (E (me,s, e)) = e
    	evaleAuxNo (R (me,s, e)) = e
    	evaleAuxNo (P (me,s, e)) = e

    	evalsAuxk :: Expr -> Bool
    	evalsAuxk (I n) = True
    	evalsAuxk (B n) = True
    	evalsAuxk (V n) = True
    	evalsAuxk e = False

    	evale :: Expr -> Expr
    	evale (I n) = (I n)
        evale (B n) = (B n)
        evale (V n) = (V n)
        evale (Add (I n) (I l)) = (I (n+l))
        evale (Add (I n) (B l)) = error "Add espera 2"
        evale (Add (B n) (I l)) = error "Add espera 2 enteros"
        evale (Add (B n) (B l)) = error "Add espera 2 enteros"
        evale (Add e1 e2) = evale (Add (evalsAuxm e1) (evalsAuxm e2))
        evale (Mul (I n) (I l)) = (I (n*l))
        evale (Mul (I n) (B l)) = error "Mul espera 2 enteros"
        evale (Mul (B n) (I l)) = error "Mul espera 2 enteros"
        evale (Mul (B n) (B l)) = error "Add espera 2 enteros"
        evale (Mul e1 e2) = evale (Mul (evalsAuxm e1) (evalsAuxm e2))
        evale (Succ (I n)) = (I (n+1))
        evale (Succ (B n)) = error "Succ espera un entero"
        evale (Succ e) = evale (Succ (evalsAuxm e))
        evale (Pred (I n)) = if n <= 0 then error "no se puede" else (I (n-1))
        evale (Pred (B n)) = error "Pred espera un entero"
        evale (Pred e) = evale (Pred (evalsAuxm e))
        evale (Not (B n)) = (B (not n))
        evale (Not (I n)) = error "nOT espera un BOOLEANO"
        evale (Not e) = evale (Not (evalsAuxm e))
        evale (And (B n) (B l)) = (B (n && l))
        evale (And (I n) (B l)) = error "And espera 2 booleanos"
        evale (And (B n) (I l)) = error "And espera 2 booleanos"
        evale (And (I n) (I l)) = error "And espera 2 booleanos"
        evale (And e1 e2) = evale (And (evalsAuxm e1) (evalsAuxm e2))
        evale (Or (B n) (B l)) = (B (n || l))
        evale (Or (I n) (B l)) = error "Or espera 2 booleanos"
        evale (Or (B n) (I l)) = error "Or espera 2 booleanos"
        evale (Or (I n) (I l)) = error "Or espera 2 booleanos"
        evale (Or e1 e2) = evale (Or (evalsAuxm e1) (evalsAuxm e2))
        evale (Lt (I n) (I l)) = (B (n < l))
        evale (Lt (I n) (B l)) = error "And espera 2 enteros"
        evale (Lt (B n) (I l)) = error "Mul espera 2 enteros"
        evale (Lt (B n) (B l)) = error "Add espera 2 enteros"
        evale (Lt e1 e2) = evale (Lt (evalsAuxm e1) (evalsAuxm e2))
        evale (Gt (I n) (I l)) = (B (n > l))
        evale (Gt (I n) (B l)) = error "And espera 2 enteros"
        evale (Gt (B n) (I l)) = error "Mul espera 2 enteros"
        evale (Gt (B n) (B l)) = error "Add espera 2 enteros"
        evale (Gt e1 e2) = evale (Gt (evalsAuxm e1) (evalsAuxm e2))
        evale (Eq (I n) (I l)) = (B (n == l))
        evale (Eq (I n) (B l)) = error "And espera 2 enteros"
        evale (Eq (B n) (I l)) = error "Mul espera 2 enteros"
        evale (Eq (B n) (B l)) = error "Add espera 2 enteros"
        evale (Eq e1 e2) = evale (Eq (evalsAuxm e1) (evalsAuxm e2))
    	evale e = (evaleAuxNo (evals (E([],[],e))))


        evalsAux :: Expr -> Expr
        evalsAux (I n) = (I n)
        evalsAux (B t) = (B t)
        evalsAux (V x) = (V x)
        evalsAux (Add (I n) (I m)) = evalsAuxm (I (n + m))
        evalsAux (Add (I n) (B b)) = error "La operacion no puede ser realizada"
        evalsAux (Add (B b) (I m)) = error "La operacion no puede ser realizada"
        evalsAux (Add (B b)(B v)) = error "La operacion no puede ser realizada"
        evalsAux (Add (I n) b) = (Add (I n) (eval1Aux b))
        evalsAux (Add a (I n)) = (Add (eval1Aux a) (I n))
        evalsAux (Add e1 e2)
            | (evaleAux e1) == (B True) && (evaleAux e2) == (B True) = evalsAuxm(Add (eval1Aux e1) (eval1Aux e2))
            | (evaleAux e1) == (B True) && (evaleAux e2) == (B False) = (Add (eval1Aux e1) e2)
            | (evaleAux e1) == (B False) && (evaleAux e2) == (B True) = (Add e1 (eval1Aux e2))
            | otherwise = (Add e1 e2)
        evalsAux (Mul (I n) (I m)) = I (n * m)
        evalsAux (Mul (I n) (B b)) = error "La operacion no puede ser realizada"
        evalsAux (Mul (B b) (I m)) = error "La operacion no puede ser realizada"
        evalsAux (Mul (B b) (B v)) = error "La operacion no puede ser realizada"
        evalsAux (Mul e1 e2)
            | (evalsAuxm e1) == (B True) && (evalsAuxm e2) == (B True) = evalsAuxm (Mul (eval1Aux e1) (eval1Aux e2))
            | (evalsAuxm e1) == (B True) && (evalsAuxm e2) == (B False) = (Mul (eval1Aux e1) e2)
            | (evalsAuxm e1) == (B False) && (evalsAux e2) == (B True) = (Mul e1 (eval1Aux e2))
            | otherwise = (Mul e1 e2)
        evalsAux (Succ (I n)) = I (n + 1)
        evalsAux (Succ (B b)) = error "La operacion no puede ser realizada"
        evalsAux (Succ e1)
            | (evalsAuxm e1) == (B True) = evalsAuxm(Succ (eval1Aux e1))
            | otherwise = (Succ e1)
        evalsAux (Pred (I n)) = I (n - 1)
        evalsAux (Pred (B b)) = error "La operacion no puede ser realizada"
        evalsAux (Pred e1)
            | (evalsAuxm e1) == (B True) = evalsAuxm (Pred (eval1Aux e1))
            | otherwise = (Pred e1)
        evalsAux (Not (I n)) = error "La operacion no puede ser realizada"
        evalsAux (Not e1)
            | (evalsAuxm e1) == (B True) = evalsAuxm (Not (eval1Aux e1))
            | otherwise = (Not e1)
        evalsAux (And (B b) (B v)) = B (b && v)
        evalsAux (And (I n) (B b)) = error "La operacion no puede ser realizada"
        evalsAux (And (B b) (I n)) = error "La operacion no puede ser realizada"
        evalsAux (And (I n) (I m)) = error "La operacion no puede ser realizada"
        evalsAux (And e1 e2)
            | (evalsAuxm e1) == (B True) && (evalsAuxm e2) == (B True) = evalsAuxm (And (eval1Aux e1) (eval1Aux e2))
            | (evalsAuxm e1) == (B True) && (evalsAuxm e2) == (B False) = (And (eval1Aux e1) e2)
            | (evalsAuxm e1) == (B False) && (evalsAuxm e2) == (B True) = (And e1 (eval1Aux e2))
            | otherwise = (And e1 e2)
        evalsAux (Or (B b) (B v)) = B (b || v)
        evalsAux (Or (I n) (B b)) = error "La operacion no puede ser realizada"
        evalsAux (Or (B b) (I n)) = error "La operacion no puede ser realizada"
        evalsAux (Or (I n) (I m)) = error "La operacion no puede ser realizada"
        evalsAux (Or e1 e2)
            | (evalsAuxm e1) == (B True) && (evalsAuxm e2) == (B True) = evalsAuxm (Or (eval1Aux e1) (eval1Aux e2))
            | (evalsAuxm e1) == (B True) && (evalsAuxm e2) == (B False) = (Or (eval1Aux e1) e2)
            | (evalsAuxm e1) == (B False) && (evalsAuxm e2) == (B True) = (Or e1 (eval1Aux e2))
            | otherwise = (Or e1 e2)
        evalsAux (Lt (I n) (I m)) = B (n < m)
        evalsAux (Lt (I n) (B b)) = error "La operacion no puede ser realizada"
        evalsAux (Lt (B b) (I m)) = error "La operacion no puede ser realizada"
        evalsAux (Lt (B b) (B v)) = error "La operacion no puede ser realizada"
        evalsAux (Lt e1 e2)
            | (evalsAuxm e1) == (B True) && (evalsAuxm e2) == (B True) = evalsAuxm(Lt (eval1Aux e1) (eval1Aux e2))
            | (evalsAuxm e1) == (B True) && (evalsAuxm e2) == (B False) = (Lt (eval1Aux e1) e2)
            | (evalsAuxm e1) == (B False) && (evalsAux e2) == (B True) = (Lt e1 (eval1Aux e2))
            | otherwise = (Lt e1 e2)
        evalsAux (Gt (I n) (I m)) = B (n > m)
        evalsAux (Gt (I n) (B b)) = error "La operacion no puede ser realizada"
        evalsAux (Gt (B b) (I m)) = error "La operacion no puede ser realizada"
        evalsAux (Gt (B b) (B v)) = error "La operacion no puede ser realizada"
        evalsAux (Gt e1 e2)
            | (evalsAuxm e1) == (B True) && (evalsAuxm e2) == (B True) = evalsAuxm (Gt (eval1Aux e1) (eval1Aux e2))
            | (evalsAuxm e1) == (B True) && (evalsAuxm e2) == (B False) = (Gt (eval1Aux e1) e2)
            | (evalsAuxm e1) == (B False) && (evalsAuxm e2) == (B True) = (Gt e1 (eval1Aux e2))
            | otherwise = (Gt e1 e2)
        evalsAux (Eq (I n) (I m)) = B (n == m)
        evalsAux (Eq (I n) (B b)) = error "La operacion no puede ser realizada"
        evalsAux (Eq (B b) (I m)) = error "La operacion no puede ser realizada"
        evalsAux (Eq (B b) (B v)) = error "La operacion no puede ser realizada"
        evalsAux (Eq e1 e2)
            | (evalsAuxm e1) == (B True) && (evalsAuxm e2) == (B True) = evalsAuxm (Eq (eval1Aux e1) (eval1Aux e2))
            | (evalsAuxm e1) == (B True) && (evalsAuxm e2) == (B False) = (Eq (eval1Aux e1) e2)
            | (evalsAuxm e1) == (B False) && (evalsAuxm e2) == (B True) = (Eq e1 (eval1Aux e2))
            | otherwise = (Eq e1 e2)
        evalsAux (If e1 e2 e3)
            | evalsAux(eval1Aux e1) == (B True) = evalsAux (eval1Aux e2)
            | evalsAux(eval1Aux e1) == (B False) = evalsAux (eval1Aux e3)
            | otherwise = (If e1 e2 e3)
        evalsAux (Let x e1 e2) = evalsAux (eval1Aux (substAux e2 (x, e1)))
        evalsAux _ = error "La operacion no puede ser realizada"


        evalsAux2 :: Expr -> Expr
        evalsAux2 (I n) = I n
        evalsAux2 (B b) = B b
        evalsAux2 (V x) = V x
        evalsAux2 (Add (B n) (B m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Add (I n) (B m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Add (B n) (I m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Add (I n) (I m)) = (I (n+m))
        evalsAux2 (Add e1 e2) = evalsAux(eval1Aux (Add e1 e2))
        evalsAux2 (Mul (B n) (B m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Mul (I n) (B m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Mul (B n) (I m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Mul (I n) (I m)) = I (n * m)
        evalsAux2 (Mul e1 e2) = evalsAux(eval1Aux (Mul e1 e2))
        evalsAux2 (Succ e) = evalsAux2(evalsAux(Succ e))
        evalsAux2 (Pred e) = evalsAux2(evalsAux(Pred e))
        evalsAux2 (Not e) = evalsAux2(evalsAux(Not e))
        evalsAux2 (Or (B n) (B m)) = B (n || m)
        evalsAux2 (Or (I n) (B m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Or (B n) (I m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Or (I n) (I m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Or e1 e2) = evalsAux(eval1Aux (Or e1 e2))
        evalsAux2 (And (B n) (B m)) = B (n && m)
        evalsAux2 (And (I n) (B m)) = error "La operacion no puede ser realizada"
        evalsAux2 (B b) = B b
        evalsAux2 (V x) = V x
        evalsAux2 (And (B n) (I m)) = error "La operacion no puede ser realizada"
        evalsAux2 (And (I n) (I m)) = error "La operacion no puede ser realizada"
        evalsAux2 (And e1 e2) = evalsAux(eval1Aux (And e1 e2))
        evalsAux2 (Lt (B n) (B m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Lt (I n) (B m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Lt (B n) (I m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Lt (I n) (I m)) = B (n < m)
        evalsAux2 (Lt e1 e2) = evalsAux(eval1Aux (Lt e1 e2))
        evalsAux2 (Gt (B n) (B m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Gt (I n) (B m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Gt (B n) (I m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Gt (I n) (I m)) = B (n > m)
        evalsAux2 (Gt e1 e2) = evalsAux(eval1Aux (Gt e1 e2))
        evalsAux2 (Eq (I n) (I m)) = B (n == m)
        evalsAux2 (Eq (I n) (B m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Eq (B n) (I m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Eq (B n) (B m)) = error "La operacion no puede ser realizada"
        evalsAux2 (Eq e1 e2) = evalsAux(eval1Aux (Eq e1 e2))
        evalsAux2 (If e1 e2 e3) = (if (evalsAux2(evalsAux e1) == (B True)) then evalsAux (eval1Aux e2) else evalsAux2 (eval1Aux e3))
        evalsAux2 (Let x e1 e2) = evalsAux (Let x (eval1Aux e1) e2)
        evalsAux2 _ = error "La operacion no puede ser realizada"

        --
        evalsAuxm :: Expr -> Expr
        evalsAuxm e = eval1Aux (evalsAux2 e)

        {- Función que se encarga de verificar si una expresión es un valor o una
        una expresión bloqueada-}
        evaleAux :: Expr -> Expr
        evaleAux (I n) = B True
        evaleAux (B b) = B True
        evaleAux (V x) = (B False)
        evaleAux (Add (I n) (I m)) = (B True)
        evaleAux (Add (I n) (B b)) = (B False)
        evaleAux (Add (B b) (I m)) = (B False)
        evaleAux (Add (B b) (B v)) = (B False)
        evaleAux (Mul e1 e2) = evaleAux(evalsAuxm (Mul e1 e2))
        evaleAux (Mul (I n) (I m)) = (B True)
        evaleAux (Mul (I n) (B b)) = (B False)
        evaleAux (Mul (B b) (I m)) = (B False)
        evaleAux (Mul (B b) (B v)) = (B False)
        evaleAux (Mul e1 e2) = evaleAux(evalsAuxm (Mul e1 e2))
        evaleAux (Succ e) = evaleAux(evalsAuxm (Succ e))
        evaleAux (Pred e) = evaleAux(evalsAuxm (Pred e))
        evaleAux (Not e) = evaleAux(evalsAuxm (Not e))
        evaleAux (And (B b) (B v)) = (B True)
        evaleAux (And (I n) (B b)) = (B False)
        evaleAux (And (B b) (I m)) = (B False)
        evaleAux (And (I n) (I m)) = (B False)
        evaleAux (And e1 e2) = evaleAux(evalsAuxm (And e1 e2))
        evaleAux (Or (B b) (B v)) = (B True)
        evaleAux (Or (I n) (B b)) = (B False)
        evaleAux (Or (B b) (I m)) = (B False)
        evaleAux (Or (I n) (I m)) = (B False)
        evaleAux (Or e1 e2) = evaleAux(evalsAuxm (Or e1 e2))
        evaleAux (Lt (I n) (I m)) = (B True)
        evaleAux (Lt (I n) (B b)) = (B False)
        evaleAux (Lt (B b) (I m)) = (B False)
        evaleAux (Lt (B b) (B v)) = (B False)
        evaleAux (Lt e1 e2) = evaleAux(evalsAuxm (Lt e1 e2))
        evaleAux (Gt (I n) (I m)) = (B True)
        evaleAux (Gt (I n) (B b)) = (B False)
        evaleAux (Gt (B b) (I m)) = (B False)
        evaleAux (Gt (B b) (B v)) = (B False)
        evaleAux (Gt e1 e2) = evaleAux(evalsAuxm (Gt e1 e2))
        evaleAux (Eq (I n) (I m)) = (B True)
        evaleAux (Eq (I n) (B b)) = (B False)
        evaleAux (Eq (B b) (I m)) = (B False)
        evaleAux (Eq (B b) (B v)) = (B False)
        evaleAux (Eq e1 e2) = evaleAux (evalsAuxm (Eq e1 e2))
        evaleAux (If e1 e2 e3)
                        | ((evalsAuxm e1) == (B True)) = evaleAux (evalsAuxm e2)
                        | ((evalsAuxm e1) == (B False)) = evaleAux (evalsAuxm e3)
                        | otherwise = (If e1 e2 e3)
        evaleAux (Let x e1 e2) = evaleAux (evalsAuxm (substAux e2 (x, e1)))
        evaleAux _ = (B False)

        eval1Aux :: Expr -> Expr
        eval1Aux (I n)             = (I n)
        eval1Aux (B t)             = (B t)
        eval1Aux (V x)             = (V x)
        eval1Aux (Add (I n) (I m)) = I (n + m)
        eval1Aux (Add (I n) e2)    = Add (I n) (eval1Aux e2)
        eval1Aux (Add (B b) e2)    = Add (B b) (eval1Aux e2)
        eval1Aux (Add (V x) e2)    = Add (V x) (eval1Aux e2)
        eval1Aux (Add e1 e2)       = Add (eval1Aux e1) e2
        eval1Aux (Mul (I n) (I m)) = I (n * m)
        eval1Aux (Mul (I n) e2)    = Mul (I n) (eval1Aux e2)
        eval1Aux (Mul (B b) e2)    = Mul (B b) (eval1Aux e2)
        eval1Aux (Mul (V x) e2)    = Mul (V x) (eval1Aux e2)
        eval1Aux (Mul e1 e2)       = Mul (eval1Aux e1) e2
        eval1Aux (Succ (I n))      = (I (n + 1))
        eval1Aux (Succ e)          = Succ (eval1Aux e)
        eval1Aux (Pred (I n))      = if n < 1 then error "No es posible hacer la operacion" else I (n - 1)
        eval1Aux (Pred e)          = Pred (eval1Aux e)
        eval1Aux (Not (B b))       = if b == True then (B False) else (B True)
        eval1Aux (Not e)           = Not (eval1Aux e)
        eval1Aux (And (B t) (B f)) = if t == True && f == True then (B True) else (B False)
        eval1Aux (And (B b) e2)    = (And (B b) (eval1Aux e2))
        eval1Aux (Or (B t) (B f))  = if t == False && f == False then (B False) else (B True)
        eval1Aux (Or (B b) e2)     = Or (B b) (eval1Aux e2)
        eval1Aux (Lt (I n)(I m))   = B (n < m)
        eval1Aux (Lt (I n) e2)     = Lt (I n) (eval1Aux e2)
        eval1Aux (Gt (I n)(I m))   = B (n > m)
        eval1Aux (Gt (I n) e2)     = Gt (I n) (eval1Aux e2)
        eval1Aux (Eq (I n) (I m))  = B (n == m)
        eval1Aux (Eq (I n) e2)     = Eq (I n) (eval1Aux e2)
        eval1Aux (If (B t) a b)    = if t then a else b
        eval1Aux (If e1 e2 e3)     = If (eval1Aux e1) e2 e3
        eval1Aux (Let x (I n) e2)  = substAux e2 (x, (I n))
        eval1Aux (Let x (B b) e2)  = substAux e2 (x, (B b))
        eval1Aux (Let x (V v) e2)  = substAux e2 (x, (V v))
        eval1Aux (Let x e1 e2)     = Let x (eval1Aux e1) e2
        eval1Aux (Fn x e)          = Fn x (eval1Aux e)
        eval1Aux (App (Fn x e) e2) = substAux e (x, e2)
        eval1Aux (Alloc e)         = Alloc (eval1Aux e)
        eval1Aux (Deref e)         = Deref (eval1Aux e)
        eval1Aux (Seq e1 e2)       = Seq (eval1Aux e1) e2
        eval1Aux (Seq Void e2)     = Seq Void (eval1Aux e2)
