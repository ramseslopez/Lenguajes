module BAE.Sintax where

  import Data.List
  import Data.Char

  type Address = Int

  type Value = Expr

  type Cell = (Address, Value)

  type Memory = [Cell]

  {- Función que dada una memoria genera una nueva dirección
     de memoria que no esté contenida en ésta -}
  newAddress :: Memory -> Expr
  newAddress [] = L 0
  newAddress xs = newAddressAux 0 (sort (getIndex xs))
                  where newAddressAux :: Int -> [Int] -> Expr
                        newAddressAux y []  = L y
                        newAddressAux y [x] = if x == y
                                              then
                                                L (y + 1)
                                              else
                                                L y
                        newAddressAux y (x:xs)
                                  | x == head xs = error "Corrupted Memory"
                                  | x == y = newAddressAux (y + 1) xs
                                  | otherwise = newAddressAux' (L y) xs
                                  where newAddressAux' :: Expr -> [Int] -> Expr
                                        newAddressAux' y l = case l of
                                          []     -> y
                                          [x]    -> y
                                          (x:xs) -> if x == head xs
                                                  then
                                                      error "Corrupted Memory"
                                                  else
                                                      newAddressAux' y xs

  {- Función que dada una dirección de memoria devuelve
     el contenido de la celda de dicha dirección -}
  access :: Address -> Memory -> Maybe Value
  access n m = case m of
          []         -> Nothing
          [(x,y)]    -> if verList(getIndex [(x,y)]) && n == x
                        then
                          Just y
                        else
                          Nothing
          ((x,y):xs) -> if verList(getIndex ((x,y):xs)) && n == x
                        then
                          Just y
                        else
                          access n xs

  {- Función que dada una celda de memoria, actualiza el valor de
     ésta misma en la memoria -}
  update :: Cell -> Memory -> Maybe Value
  update c m = case m of
          []         -> Nothing
          [(x,y)]    -> if verList(getIndex [(x,y)]) && (fst c) == x
                        then
                          Just (snd c)
                        else
                          Nothing
          ((x,y):xs) -> if verList(getIndex ((x,y):xs)) && (fst c) == x
                        then
                          Just (snd c)
                        else update c xs

  {- Función que verifica si hay direcciones repetidas -}
  verList :: [Int] -> Bool
  verList l = case l of
         [x]    -> True
         (x:xs) -> if x /= head (sort xs)
                   then
                      verList (sort xs)
                   else
                      error "Corrupted Memory"

  {- Función que obtiene las direcciones de la memoria -}
  getIndex :: Memory -> [Int]
  getIndex l = case l of
          [(x, y)]    -> [x]
          ((x, y):xs) -> [x] ++ getIndex xs

  getExpr:: Memory -> Int -> Expr
  getExpr [] _ = Void
  getExpr ((x,y):xs) n = if (n == x) then y else (getExpr xs n)

  data Expr = V Identifier | I Int | B Bool
              | Add Expr Expr | Mul Expr Expr | Succ Expr | Pred Expr
              | Not Expr | And Expr Expr | Or Expr Expr
              | Lt Expr Expr | Gt Expr Expr | Eq Expr Expr
              | If Expr Expr Expr
              | Let Identifier Expr Expr
              | Fn Identifier Expr
              | App Expr Expr
              | L Int | Alloc Expr | Deref Expr | Assig Expr Expr
              | Void | Seq Expr Expr | While Expr Expr
              | Raise Expr | Handle Expr Identifier Expr
              | LetCC Identifier Expr
              | Continue Expr Expr
              | Cont Stack deriving (Eq)

  type Identifier = String

  instance Show Expr where
    show e = case e of
      V x            -> "V[" ++ x ++ "]"
      I n            -> "N[" ++ (show n) ++ "]"
      B t            -> "B[" ++ (show t) ++ "]"
      Add e1 e2      -> "add(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      Mul e1 e2      -> "mul(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      Succ e         -> "succ(" ++ (show e) ++ ")"
      Pred e         -> "pred(" ++ (show e) ++ ")"
      Not e          -> "not(" ++ (show e) ++ ")"
      And e1 e2      -> "and(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      Or e1 e2       -> "or(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      Lt e1 e2       -> "lt(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      Gt e1 e2       -> "gt(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      Eq e1 e2       -> "eq(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      If e1 e2 e3    -> "if(" ++ (show e1) ++ ", " ++ (show e2) ++ ", " ++ (show e3) ++ ")"
      Let x e1 e2    -> "let(" ++ (show e1) ++ ", " ++ x ++ "." ++ (show e2) ++ ")"
      Fn x e         -> "fn(" ++ x ++ "." ++ (show e) ++ ")"
      App e1 e2      -> "app(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      L n            -> "l => " ++ (show n)
      Alloc e        -> "alloc" ++ (show e) ++ ")"
      Void           -> "void"
      Assig e1 e2    -> (show e1) ++ " ::= " ++ (show e2)
      Deref e        -> "!" ++ (show e)
      Seq e1 e2      -> (show e1) ++ ";" ++ (show e2)
      While e1 e2    -> "while(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      Raise e        -> "raise(" ++ (show e) ++ ")"
      Handle e1 x e2 -> "handle(" ++ (show e1) ++ ", " ++ x ++ "." ++ (show e2) ++ ")"
      LetCC x e      -> "letcc(" ++ x ++ "." ++ (show e) ++ ")"
      Continue e1 e2 -> "continue(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
      Cont s         -> "cont(" ++ (show s) ++ ")"


  type Stack = [Frame]

  type Pending = ()

  data Frame = SuccF Pending
               | PredF Pending
               | NotF Pending
               | FnT Identifier Pending
               | IfT Pending Expr Expr
               | LetT Identifier Pending Expr
               | AddFL Pending Expr | AddFR Expr Pending
               | MulFL Pending Expr | MulFR Expr Pending
               | AndFL Pending Expr | AndFR Expr Pending
               | OrFL Pending Expr | OrFR Expr Pending
               | LtFL Pending Expr | LtFR Expr Pending
               | GtFL Pending Expr | GtFR Expr Pending
               | EqFL Pending Expr | EqFR Expr Pending
               | AppFL Pending Expr | AppFR Expr Pending
               | LF Pending
               | AllocF Pending
               | VoidF
               | AssigFL Pending Expr
               | AssigFR Expr Pending
               | DerefF Pending
               | SeqFL Pending Expr
               | SeqFR Expr Pending
               | WhileFL Pending Expr
               | WhileFR Expr Pending
               | RaiseF Pending
               | HandleF Pending Identifier Expr
               | LetCCF Identifier Pending
               | ContinueFL Pending Expr
               | ContinueFR Expr Pending
               | ContF Stack deriving(Eq)

  showP :: Pending -> String
  showP p = "-"

  instance Show Frame where
    show e = case e of
        SuccF p        -> "succ(" ++ (showP p) ++ ")"
        PredF p        -> "pred(" ++ (showP p) ++ ")"
        NotF p         -> "not(" ++ (showP p) ++ ")"
        LF p           -> "l =>" ++ (showP p)
        VoidF          -> "void"
        AllocF p       -> "alloc(" ++ (showP p) ++ ")"
        FnT x p        -> "fn(" ++ x ++ ", " ++ (showP p) ++ ")"
        DerefF p       -> "!" ++ (showP p)
        IfT p e1 e2    -> "if(" ++ (showP p) ++ ", " ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        LetT x p e1    -> "let(" ++ x ++ ", " ++ (showP p) ++ ", " ++ (show e1) ++ ")"
        AddFL p e      -> "add(" ++ (showP p) ++ ", " ++ (show e) ++ ")"
        AddFR e p      -> "add(" ++ (show e)  ++ ", " ++ (showP p) ++ ")"
        MulFL p e      -> "mul(" ++ (showP p) ++ ", " ++ (show e) ++ ")"
        MulFR e p      -> "mul(" ++ (show e) ++ ", "++ (showP p) ++ ")"
        AndFL p e      -> "and(" ++ (showP p) ++ ", " ++ (show e) ++ ")"
        AndFR e p      -> "and(" ++ (show e) ++ ", " ++ (showP p) ++ ")"
        OrFL p e       -> "and(" ++ (showP p) ++ ", " ++ (show e) ++ ")"
        OrFR e p       -> "or(" ++ (show e) ++ ", " ++ (showP p) ++ ")"
        LtFL p e       -> "lt(" ++ (showP p) ++ ", " ++ (show e) ++ ")"
        LtFR e p       -> "lt(" ++ (show e) ++ ", " ++ (showP p) ++ ")"
        GtFL p e       -> "gt(" ++ (showP p) ++ ", " ++ (show e) ++ ")"
        GtFR e p       -> "gt(" ++ (show e) ++ ", " ++ (showP p) ++ ")"
        EqFL p e       -> "eq(" ++ (showP p) ++ ", " ++ (show e) ++ ")"
        EqFR e p       -> "eq(" ++ (show e) ++ ", " ++ (showP p) ++ ")"
        AppFL p e      -> "app(" ++ (showP p) ++ ", " ++ (show e) ++ ")"
        AppFR e p      -> "app(" ++ (show e) ++ ", " ++ (showP p) ++ ")"
        AssigFL p e    -> (showP p) ++ "::=" ++ (show e)
        AssigFR e p    -> (show e) ++ "::=" ++ (showP p)
        SeqFL p e      -> (showP p) ++ "; " ++ (show e)
        SeqFR e p      -> (show e) ++ "; " ++ (showP p)
        WhileFL p e    -> "while(" ++ (showP p) ++ ", " ++ (show e) ++ ")"
        WhileFR e p    -> "while(" ++ (show e) ++ ", " ++ (showP p) ++ ")"
        RaiseF p       -> "raise(" ++ (showP p) ++ ")"
        HandleF p x e  -> "handle(" ++ (showP p) ++ ", " ++ x ++ "." ++ (show e) ++ ")"
        LetCCF x p     -> "letcc(" ++ x ++ "." ++ (showP p) ++ ")"
        ContinueFL p e -> "continue(" ++ (showP p) ++ ", " ++ (show e) ++ ")"
        ContinueFR e p -> "continue(" ++ (show e) ++ ", " ++ (showP p) ++ ")"
        ContF s        -> "cont(" ++ (show s) ++ ")"

  data State = E (Memory, Stack, Expr) | R (Memory, Stack, Expr) | P (Memory, Stack, Expr) deriving (Eq,Show)

  type Substitution = (Identifier, Expr)

  {- Función que devuelve las variables libre de un estado -}
  frVars :: State -> [Identifier]
  frVars (E (p, m, e)) = case e of
          I n            -> []
          B t            -> []
          V x            -> [x]
          L n            -> []
          Void           -> []
          Cont s         -> []
          Succ e         -> frVars (E (p, m, e))
          Pred e         -> frVars (E (p, m, e))
          Add e1 e2      -> union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)))
          Mul e1 e2      -> union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)))
          Not e          -> frVars (E (p, m, e))
          And e1 e2      -> union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)))
          Or e1 e2       -> union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)))
          Lt e1 e2       -> union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)))
          Eq e1 e2       -> union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)))
          Gt e1 e2       -> union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)))
          If e1 e2 e3    -> union (frVars (E (p, m, e1)))  (union (frVars (E (p, m, e2))) (frVars (E(p, m, e3))))
          Let x e1 e2    -> if elem x (frVars (E (p, m, e2)))
                            then
                              union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)) \\ [x])
                            else
                              union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)))
          Fn x e         -> if elem x (frVars (E (p, m, e)))
                            then
                              (frVars (E (p, m, e)) \\ [x])
                            else
                              frVars (E (p, m, e))
          App e1 e2      -> union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)))
          Alloc e        -> frVars (E (p, m, e))
          Deref e        -> frVars (E (p, m, e))
          Assig e1 e2    -> union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)))
          Seq e1 e2      -> union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)))
          While e1 e2    -> union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)))
          Raise e        -> frVars (E (p, m, e))
          Handle e1 x e2 -> if elem x (frVars (E (p, m , e2)))
                            then
                              union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)) \\ [x])
                            else
                              union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)))
          LetCC x e      -> (frVars (E (p, m, e)) \\ [x])
          Continue e1 e2 -> union (frVars (E (p, m, e1))) (frVars (E (p, m, e2)))

  {- Función que realiza la sustitución a un estado -}
  subst :: State -> Substitution -> State
  subst (E (p, m, e)) s@(y, a) = case e of
          I n            -> E (p , m, I n)
          B t            -> E (p, m, B t)
          V x            -> if x == y then E (p, m, a) else E (p, m, V x)
          L n            -> E (p, m, L n)
          Void           -> E (p, m, Void)
          Succ e         -> E (p, m, Succ (subst' e s))
          Pred e         -> E (p, m, Pred (subst' e s))
          Add e1 e2      -> E(p, m, Add (subst' e1 s) (subst' e2 s))
          Mul e1 e2      -> E (p, m, Mul (subst' e1 s) (subst' e2 s))
          Not e          -> E (p, m, Not (subst' e s))
          And e1 e2      -> E (p, m, And (subst' e1 s) (subst' e2 s))
          Or e1 e2       -> E (p, m, Or (subst' e1 s) (subst' e2 s))
          Lt e1 e2       -> E (p, m, Lt (subst' e1 s) (subst' e2 s))
          Gt e1 e2       -> E (p, m, Gt (subst' e1 s) (subst' e2 s))
          Eq e1 e2       -> E (p, m, Eq (subst' e1 s) (subst' e2 s))
          If e1 e2 e3    -> E (p, m, If (subst' e1 s) (subst' e2 s) (subst' e3 s))
          Let x e1 e2    -> E (p, m, Let x (subst'  e1 s) t)
                            where t = if notElem x ([y] ++ (frVars' a))
                                      then
                                        (subst' e2 s)
                                      else
                                        error "La sustitucion no puede ser realizada"
          Fn x e         -> if elem x (frVars' a)
                            then
                             E (p, m, Fn (incrVar x) (subst' e s))
                            else
                             E (p, m, Fn x (subst' e s))
          App e1 e2      -> E (p, m, App (subst' e1 s) (subst' e2 s))
          Alloc e        -> E (p, m, Alloc (subst' e s))
          Deref e        -> E (p, m, Deref (subst' e s))
          Assig e1 e2    -> E (p, m, Assig (subst' e1 s) (subst' e2 s))
          Seq e1 e2      -> E(p, m, Seq (subst' e1 s) (subst' e2 s))
          While e1 e2    -> E (p, m, While (subst' e1 s) (subst' e2 s))
          Raise e        -> E (p ,m, Raise (subst' e s))
          Handle e1 x e2 -> E (p, m, Handle (subst' e1 s) x (subst' e2 s))
          LetCC x e      -> E (p, m, LetCC x (subst' e s))
          Continue e1 e2 -> E (p, m, Continue (subst' e1 s) (subst' e2 s))
          Cont ss         -> E (p, m, Cont ss)

  substAux :: Expr -> Substitution -> Expr
  substAux e s@(y, a) = case e of
          I n         -> I n
          B t         -> B t
          V x         -> if x == y then a else V x
          L n         -> L n
          Void        -> Void
          Succ e      -> Succ (substAux e s)
          Pred e      -> Pred (substAux e s)
          Add e1 e2   -> Add (substAux e1 s) (substAux e2 s)
          Mul e1 e2   -> Mul (substAux e1 s) (substAux e2 s)
          Not e       -> Not (substAux e s)
          And e1 e2   -> And (substAux e1 s) (substAux e2 s)
          Or e1 e2    -> Or (substAux e1 s) (substAux e2 s)
          Lt e1 e2    -> Lt (substAux e1 s) (substAux e2 s)
          Gt e1 e2    -> Gt (substAux e1 s) (substAux e2 s)
          Eq e1 e2    -> Eq (substAux e1 s) (substAux e2 s)
          If e1 e2 e3 -> If (substAux e1 s) (substAux e2 s) (substAux e3 s)
          Let x e1 e2 -> Let x (substAux e1 s) t
                          where t = if notElem x ([y] ++ (frVarsAux a))
                                    then
                                      substAux e2 s
                                    else
                                      error "La sustitucion no puede ser realizada"
          Fn x e      -> if elem x (frVarsAux a)
                          then
                            Fn (incrVar x) (substAux e s)
                          else
                            Fn x (substAux e s)
          App e1 e2   -> App (substAux e1 s) (substAux e2 s)
          Alloc e     -> Alloc (substAux e s)
          Deref e     -> Deref (substAux e s)
          Assig e1 e2 -> Assig (substAux e1 s) (substAux e2 s)
          Seq e1 e2   -> Seq (substAux e1 s) (substAux e2 s)
          While e1 e2 -> While (substAux e1 s) (substAux e2 s)

  frVarsAux :: Expr -> [Identifier]
  frVarsAux e = case e of
          I n         -> []
          B t         -> []
          V x         -> [x]
          L n         -> []
          Void        -> []
          Succ e      -> frVarsAux e
          Pred e      -> frVarsAux e
          Add e1 e2   -> union (frVarsAux e1) (frVarsAux e2)
          Mul e1 e2   -> union (frVarsAux e1) (frVarsAux e2)
          Not e       -> frVarsAux e
          And e1 e2   -> union (frVarsAux e1) (frVarsAux e2)
          Or e1 e2    -> union (frVarsAux e1) (frVarsAux e2)
          Lt e1 e2    -> union (frVarsAux e1) (frVarsAux e2)
          Eq e1 e2    -> union (frVarsAux e1) (frVarsAux e2)
          Gt e1 e2    -> union (frVarsAux e1) (frVarsAux e2)
          If e1 e2 e3 -> union (frVarsAux e1)  (union (frVarsAux e2) (frVarsAux e3))
          Let x e1 e2 -> if elem x (frVarsAux e2)
                          then
                            union (frVarsAux e1) (frVarsAux e2 \\ [x])
                          else
                            union (frVarsAux e1) (frVarsAux e2)
          Fn x e      -> if elem x (frVarsAux e)
                          then
                            (frVarsAux e \\ [x])
                          else
                            frVarsAux e
          App e1 e2   -> union (frVarsAux e1) (frVarsAux e2)
          Alloc e     -> frVarsAux e
          Deref e     -> frVarsAux e
          Assig e1 e2 -> union (frVarsAux e1) (frVarsAux e2)
          Seq e1 e2   -> union (frVarsAux e1) (frVarsAux e2)
          While e1 e2 -> union (frVarsAux e1) (frVarsAux e2)

  {- Función que verifica si dos estados son alpha-equivalentes -}
  alphaEq :: State -> State -> Bool
  alphaEq (E (p1, m1 , I n1)) (E (p2, m2, I n2)) = p1 == p2 && m1 == m2 && n1 == n2
  alphaEq (E (p1, m1 , B n1)) (E (p2, m2, B n2)) = p1 == p2 && m1 == m2 && n1 == n2
  alphaEq (E (p1, m1 , V x)) (E (p2, m2, V y)) = p1 == p2 && m1 == m2
  alphaEq (E (p1, m1, L n1)) (E (p2, m2, L n2)) = p1 == p2 && m1 == m2 && n1 == n2
  alphaEq (E (p1, m1, Void)) (E (p2, m2, Void)) = p1 == p2 && m1 == m2
  alphaEq (E (p1, m1, Succ e1)) (E (p2, m2, Succ e2)) = p1 == p2 && m1 == m2 && (alphaEq' e1 e2)
  alphaEq (E (p1, m1, Pred e1)) (E (p2, m2, Pred e2)) = p1 == p2 && m1 == m2 && (alphaEq' e1 e2)
  alphaEq (E (p1, m1, Add n1 n2)) (E (p2, m2, Add n3 n4)) = p1 == p2 && m1 == m2 && (alphaEq' n1 n3) && (alphaEq' n2 n4)
  alphaEq (E (p1, m1, Mul n1 n2)) (E (p2, m2, Mul n3 n4)) = p1 == p2 && m1 == m2 && (alphaEq' n1 n3) && (alphaEq' n2 n4)
  alphaEq (E (p1, m1, Not e1)) (E (p2, m2, Not e2)) = p1 == p2 && m1 == m2 && (alphaEq' e1 e2)
  alphaEq (E (p1, m1, And n1 n2)) (E (p2, m2, And n3 n4)) = p1 == p2 && m1 == m2 && (alphaEq' n1 n3) && (alphaEq' n2 n4)
  alphaEq (E (p1, m1, Or n1 n2)) (E (p2, m2, Or n3 n4)) = p1 == p2 && m1 == m2 && (alphaEq' n1 n3) && (alphaEq' n2 n4)
  alphaEq (E (p1, m1, Lt n1 n2)) (E (p2, m2, Lt n3 n4)) = p1 == p2 && m1 == m2 && (alphaEq' n1 n3) && (alphaEq' n2 n4)
  alphaEq (E (p1, m1, Gt n1 n2)) (E (p2, m2, Gt n3 n4)) = p1 == p2 && m1 == m2 && (alphaEq' n1 n3) && (alphaEq' n2 n4)
  alphaEq (E (p1, m1, Eq n1 n2)) (E (p2, m2, Eq n3 n4)) = p1 == p2 && m1 == m2 && (alphaEq' n1 n3) && (alphaEq' n2 n4)
  alphaEq (E (p1, m1, If e1 e2 e3)) (E (p2, m2, If e4 e5 e6)) = p1 == p2 && m1 == m2 && (alphaEq' e1 e4) && (alphaEq' e2 e5) && (alphaEq' e3 e6)
  alphaEq (E (p1, m1, Let x e1 e2)) (E (p2, m2, Let y e3 e4)) = p1 == p2 && m1 == m2 && alphaEq' l s
                                                                where l = subst' e2 (x,e1)
                                                                      s = subst' e4 (y, e3)
  alphaEq (E (p1, m1, Fn x e1)) (E (p2, m2, Fn y e2)) = p1 == p2 && m1 == m2 && (alphaEq' e1 e2)
  alphaEq (E (p1, m1, App e1 e2)) (E (p2, m2, App d1 d2)) = p1 == p2 && m1 == m2 &&(alphaEq' e1 d1) && (alphaEq' e2 d2)
  alphaEq (E (p1, m1, While e1 e2)) (E (p2, m2, While d1 d2)) = p1 == p2 && m1 == m2 && (alphaEq' e1 d1) && (alphaEq' e2 d2)
  alphaEq (E (p1, m1, Alloc e)) (E (p2, m2, Alloc d)) = p1 == p2 && m1 == m2 && (alphaEq' e d)
  alphaEq (E (p1, m1, Deref e)) (E (p2, m2, Deref d)) = p1 == p2 && m1 == m2 && (alphaEq' e d)
  alphaEq (E (p1, m1, Assig e1 e2)) (E (p2, m2, Assig d1 d2)) = p1 == p2 && m1 == m2 && (alphaEq' e1 d1) && (alphaEq' e2 d2)
  alphaEq (E (p1, m1, Seq e1 e2)) (E (p2, m2, Seq d1 d2)) = p1 == p2 && m1 == m2 && (alphaEq' e1 d1) && (alphaEq' e2 d2)
  alphaEq (E (p1, m1, Raise e)) (E (p2, m2, Raise d)) = p1 == p2 && m1 == m2 && (alphaEq' e d)
  alphaEq (E (p1, m1, Handle e1 x e2)) (E (p2, m2, Handle d1 y d2)) = p1 == p2 && m1 == m2 && (alphaEq' e1 d1) && (alphaEq' e2 d2)
  alphaEq (E (p1, m1, LetCC x e1)) (E (p2, m2, LetCC y e2)) = p1 == p2 && m1 == m2 && (alphaEq' e1 e2)
  alphaEq (E (p1, m1, Continue e1 e2)) (E (p2, m2, Continue e3 e4)) = p1 == p2 && m1 == m2 && (alphaEq' e1 e3) && (alphaEq' e2 e4)
  alphaEq (E (p1, m1, Cont s)) (E (p2, m2, Cont ss)) = p1 == p2 && m1 == m2 && s == ss

  {- Función que se encarga de incrementar variables en una unidad -}
  incrVar :: Identifier -> Identifier
  incrVar xs
              | isDigit(last xs) = (take ((length xs) - 1) xs) ++ show(intLast xs)
              | otherwise        = xs ++ "1"
              where intLast :: String -> Int
                    intLast xs = read(take 1 (reverse xs)) + 1

  {- Funcion que realiza la sustitución a una función -}
  subst' :: Expr -> Substitution -> Expr
  subst' e s@(y, a) = case e of
                  I n         -> I n
                  B t         -> B t
                  V x         -> if x == y then a else V x
                  L n         -> L n
                  Void        -> Void
                  Succ e      -> Succ (subst' e s)
                  Pred e      -> Pred (subst' e s)
                  Add e1 e2   -> Add (subst' e1 s) (subst' e2 s)
                  Mul e1 e2   -> Mul (subst' e1 s) (subst' e2 s)
                  Not e       -> Not (subst' e s)
                  And e1 e2   -> And (subst' e1 s) (subst' e2 s)
                  Or e1 e2    -> Or (subst' e1 s) (subst' e2 s)
                  Lt e1 e2    -> Lt (subst' e1 s) (subst' e2 s)
                  Gt e1 e2    -> Gt (subst' e1 s) (subst' e2 s)
                  Eq e1 e2    -> Eq (subst' e1 s) (subst' e2 s)
                  If e1 e2 e3 -> If (subst' e1 s) (subst' e2 s) (subst' e3 s)
                  Let x e1 e2 -> Let x (subst' e1 s) t
                                  where t = if notElem x ([y] ++ (frVars' a))
                                            then
                                              subst' e2 s
                                            else
                                              error "La sustitucion no puede ser realizada"
                  Fn x e      -> if elem x (frVars' a)
                                  then
                                    Fn (incrVar x) (subst' e s)
                                  else
                                    Fn x (subst' e s)
                  App e1 e2   -> App (subst' e1 s) (subst' e2 s)
                  Alloc e     -> Alloc (subst' e s)
                  Deref e     -> Deref (subst' e s)
                  Assig e1 e2 -> Assig (subst' e1 s) (subst' e2 s)
                  Seq e1 e2   -> Seq (subst' e1 s) (subst' e2 s)
                  While e1 e2 -> While (subst' e1 s) (subst' e2 s)
                  Raise e -> Raise (subst' e s)
                  Handle e1 x e2 -> Handle (subst' e1 s) x (subst' e2 s)
                  LetCC x e -> LetCC x (subst' e s)

  {- Función que devuelve la lista variables libres de una expresión -}
  frVars' :: Expr -> [Identifier]
  frVars' e = case e of
                  I n         -> []
                  B t         -> []
                  V x         -> [x]
                  L n         -> []
                  Void        -> []
                  Cont s      -> []
                  Succ e      -> frVars' e
                  Pred e      -> frVars' e
                  Add e1 e2   -> union (frVars' e1) (frVars' e2)
                  Mul e1 e2   -> union (frVars' e1) (frVars' e2)
                  Not e       -> frVars' e
                  And e1 e2   -> union (frVars' e1) (frVars' e2)
                  Or e1 e2    -> union (frVars' e1) (frVars' e2)
                  Lt e1 e2    -> union (frVars' e1) (frVars' e2)
                  Eq e1 e2    -> union (frVars' e1) (frVars' e2)
                  Gt e1 e2    -> union (frVars' e1) (frVars' e2)
                  If e1 e2 e3 -> union (frVars' e1)  (union (frVars' e2) (frVars' e3))
                  Let x e1 e2 -> if elem x (frVars' e2)
                                 then
                                    union (frVars' e1) (frVars' e2 \\ [x])
                                 else
                                    union (frVars' e1) (frVars' e2)
                  Fn x e      -> if elem x (frVars' e)
                                 then
                                    (frVars' e \\ [x])
                                 else
                                    frVars' e
                  App e1 e2   -> union (frVars' e1) (frVars' e2)
                  Alloc e     -> frVars' e
                  Deref e     -> frVars' e
                  Assig e1 e2 -> union (frVars' e1) (frVars' e2)
                  Seq e1 e2   -> union (frVars' e1) (frVars' e2)
                  While e1 e2 -> union (frVars' e1) (frVars' e2)
                  Raise e -> (frVars' e)
                  Handle e1 x e2 -> union (frVars' e1) ((frVars' e2) \\ [x])
                  LetCC x e -> (frVars' e) \\ [x]
                  Continue e1 e2 -> union (frVars' e1) (frVars' e2)

  {- Función que decide si dos expresiones son alpha-equivalentes -}
  alphaEq' :: Expr -> Expr -> Bool
  alphaEq' (I n) (I m)
                                  | n == m = True
                                  | otherwise = False
  alphaEq' (B t) (B f)
                                  | t == f = True
                                  | otherwise = False
  alphaEq' (V x) (V y)             = True
  alphaEq' (L n) (L m)             = n == m
  alphaEq' (Add n m) (Add n1 m1)   = (alphaEq' n n1) && (alphaEq' m m1)
  alphaEq' (Mul n m) (Mul n1 m1)   = (alphaEq' n n1) && (alphaEq' m m1)
  alphaEq' (Succ n) (Succ m)       = alphaEq' n m
  alphaEq' (Pred n) (Pred m)       = alphaEq' n m
  alphaEq' (Not p) (Not q)         = alphaEq' p q
  alphaEq' (And p q) (And s t)     = (alphaEq' p s) && (alphaEq' q t)
  alphaEq' (Or p q) (Or s t)       = (alphaEq' p s) && (alphaEq' q t)
  alphaEq' (Lt n m) (Lt n1 m1)     = (alphaEq' n n1) && (alphaEq' m m1)
  alphaEq' (Gt n m) (Gt n1 m1)     = (alphaEq' n n1) && (alphaEq' m m1)
  alphaEq' (Eq n m) (Eq n1 m1)     = (alphaEq' n n1) && (alphaEq' m m1)
  alphaEq' (If a b c) (If d e f)   = (alphaEq' a d) && (alphaEq' b e) && (alphaEq' c f)
  alphaEq' (Let x a b) (Let y c d) = alphaEq' l s
                                    where l = subst' b (x,a)
                                          s = subst' d (y, c)
  alphaEq' (Fn x e1) (Fn y e2)     = (alphaEq' e1 e2)
  alphaEq' (App e1 e2) (App d1 d2) = (alphaEq' e1 d1) && (alphaEq' e2 d2)
  alphaEq' (While e1 e2) (While d1 d2) = (alphaEq' e1 d1) && (alphaEq' e2 d2)
  alphaEq' (Alloc e) (Alloc d) = (alphaEq' e d)
  alphaEq' (Deref e) (Deref d) = (alphaEq' e d)
  alphaEq' (Assig e1 e2) (Assig d1 d2) = (alphaEq' e1 d1) && (alphaEq' e2 d2)
  alphaEq' (Seq e1 e2) (Seq d1 d2) = (alphaEq' e1 d1) && (alphaEq' e2 d2)
  alphaEq' (Raise e) (Raise d) = (alphaEq' e d)
  alphaEq' (Handle e1 x e2) (Handle d1 y d2) = (alphaEq' e1 d1) && (alphaEq' e2 d2)
  alphaEq' (LetCC x e1) (LetCC y e2) = (alphaEq' e1 e2)
  alphaEq' (Continue e1 e2) (Continue e3 e4) = (alphaEq' e1 e3) && (alphaEq' e2 e4)
  alphaEq' (Cont s) (Cont ss) = s == ss
  alphaEq' _ _ = False
