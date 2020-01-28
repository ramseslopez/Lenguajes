

type Pending = []

data Frame = SuccF Pending
             | PredF Pending
             | NotF Pending
             | Fn Identifier Pending
             | IfT Pending Expr Expr
             | Let Identifier Pending Expr
             | AddF Pending Expr | AddF Expr Pending
             | MulF Pending Expr | MulF Expr Pending
             | AndF Pending Expr | OrF Expr Pending
             | LtF Pending Expr | LtF Expr Pending
             | GtF Pending Expr | GtF Expr Pending
             | EqF Pending Expr | EqF Expr Pending
             | AppF Pending Expr | AppF Expr Pending
             | Error

type Stack = [Frame]

data State = E (Stack, Memory, Expr) | R (Stack, Memory, Expr) | P (Stack, Memory, Expr)

eval1 :: State -> State
eval1 (E  (m,s,e)) = case e of
    V _ -> R (m,s, e)
    I _ -> R (m,s, e)
    B _ -> R (m,s ,e)
    Fn x e -> (E (m,((FnF x Pending):s), e)))
    Fix x e -> E (s, Sintax.subst e (x, Fix x e))
    Succ e -> E (((SuccF Pending): s), e)
    PredF e -> E (((PredFL Pending): s), e)
    Add e1 e2 -> E (((AddFL Pending e2) : s), e1)
    Mul e1 e2 -> E (((MulFL Pending e2) : s), e1)
    NotF e -> E (((NotF Pending): s), e)
    And e1 e2 -> E (((AndFL Pending e2) : s), e1)
    Or e1 e2 -> E (((OrFL Pending e2) : s), e1)
    Gt e1 e2 -> E (((GtFL Pending e2) : s), e1)
    Lt e1 e2 -> E (((LtFL Pending e2) : s), e1)
    Eq e1 e2 -> E (((EqFL Pending e2) : s), e1)
    App e1 e2 -> E (((AppFL Pending e2) : s), e1)
    If e1 e2 e3 -> E (((IfT Pending e2 e3) : s), e1)
    Let x e1 e2 -> E (((LetF x Pending e2):s), e1)
eval1 (R (s, e)) = case e of
    (V x) -> case s of
        ((LetF x _ e2) : s') -> E (s', Sintax.subst e2 (x, e))
        _ -> P (s, Error)
    I m ->  case s of
        ((FnF x _) : s') -> R (s', Fn x e)
        ((SuccF _) : s') -> R (s', I (n + 1))
        ((PredF _) : s') -> R (s', I (n - 1))
        ((AddFL _ e2) : s') -> E ((AddFR e Pending : s'), e2)
        ((AddFR (I n) _) : s ) R (s', I (n + m))
        ((MulFL _ e2) : s') -> E ((MulFR e Pending : s'), e2)
        ((MulFR (I n) _) : s ) R (s', I (n * m))
        ((LtFL _ e2) : s') -> E ((LtFR e Pending : s'), e2)
        ((LtFR (I n) _) : s ) R (s', B (n < m))
        ((GtFL _ e2) : s') -> E ((GtFR e Pending : s'), e2)
        ((GtFR (I n) _) : s ) R (s', B (n > m))
        ((EqFL _ e2) : s') -> E ((EqFR e Pending : s'), e2)
        ((EqFR (I n) _) : s ) R (s', B (n == m))
        ((LetF x _ e2) : s') -> E (s', Sintax.subst e
        2 (x, e))
        _ -> P (s' Error)
    (B q) -> case s of
        ((FnF x _):s') -> R (s', Fn x e)
        ((NotF _):s') -> R (s', Not e)
        ((AndFL _ e2) : s') -> E ((AndFR e Pending : s'), e2)
        ((AndFR (B n) _) : s ) R (s', I (n && m))
        ((OrFL _ e2) : s') -> E ((OrFR e Pending : s'), e2)
        ((OrFR (B n) _) : s ) R (s', I (n || m))
        ((IfF _ e2 e3):s') -> E (s', if q then e2 else e3)
        ((LetF x _ e2))
