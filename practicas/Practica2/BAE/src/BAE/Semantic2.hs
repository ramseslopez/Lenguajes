    module Semantic where

    import Sintax
    

    {- Función que se encarga de evaluar un solo paso de una expresión -}
    eval1 :: Expr -> Expr
    eval1 (I n) = error "Error"
    eval1 (B t) = error "Error"
    eval1 (V x) = error "Error"
    eval1 (Add (I n) (I m)) = (I (n + m))
    eval1 (Add (I n) e2) = (Add (I n) (eval1 e2))
    eval1 (Mul (I n) (I m)) = (I (n * m))
    eval1 (Mul (I n) e2) = (Mul (I n) (eval1 e2))
    eval1 (Succ (I n)) = (I (n + 1))
    eval1 (Succ e) = (Succ (eval1 e))
    eval1 (Pred (I n)) = if n < 1 then error "No es posible hacer la operacion" else (I (n - 1)) 
    eval1 (Pred e) = (Pred (eval1 e))
    eval1 (Not (B b)) = if b == True then (B False) else (B True)
    eval1 (Not e) = (Not (eval1 e))
    eval1 (And (B t) (B f)) = if t == True && f == True then (B True) else (B False)
    eval1 (And (B b) e2) = (And (B b) (eval1 e2))
    eval1 (Or (B t) (B f)) = if t == False && f == False then (B False) else (B True)
    eval1 (Or (B b) e2) = (Or (B b) (eval1 e2))
    eval1 (Lt (I n)(I m)) = B (n < m)
    eval1 (Lt (I n) e2) = (Lt (I n) (eval1 e2))
    eval1 (Gt (I n)(I m)) = B (n > m)
    eval1 (Gt (I n) e2) = (Gt (I n) (eval1 e2))
    eval1 (Eq (I n) (I m)) = B (n == m)
    eval1 (Eq (I n) e2) = (Eq (I n) (eval1 e2))
    eval1 (If (B t) a b) = if t then a else b
    eval1 (If e1 e2 e3) = (If (eval1 e1) e2 e3)
    eval1 (Let x (I n) e2) = subst e2 (x, (I n))
    eval1 (Let x (B b) e2) = subst e2 (x, (B b))
    eval1 (Let x e1 e2) = Let x (eval1 e1) e2


    evalsAux :: Expr -> Expr
    evalsAux (I n) = (I n)
    evalsAux (B t) = (B t)
    evalsAux (V x) = (V x)
    evalsAux (Add (I n) (I m)) = evalsAux (I (n + m))
    evalsAux (Add (I n) (B b)) = Add (I n) (B b)
    evalsAux (Add (B b) (I m)) = Add (B b) (I m)
    evalsAux (Add (B b)(B v)) = Add (B b) (B v)
    evalsAux (Add (I n) b) = (Add (I n) (eval1 b))
    evalsAux (Add a (I n)) = (Add (eval1 a) (I n))
    evalsAux (Add e1 e2)
        | (evals e1) == (B True) && (evals e2) == (B True) = evals(Add (eval1 e1) (eval1 e2))
        | (evals e1) == (B True) && (evals e2) == (B False) = (Add (eval1 e1) e2)
        | (evals e1) == (B False) && (evals e2) == (B True) = (Add e1 (eval1 e2))
        | otherwise = (Add e1 e2)
    evalsAux (Mul (I n) (I m)) = I (n * m)
    evalsAux (Mul (I n) (B b)) = Mul (I n) (B b)
    evalsAux (Mul (B b) (I m)) = Mul (B b) (I m)
    evalsAux (Mul (B b) (B v)) = Mul (B b) (B v)
    evalsAux (Mul e1 e2)
        | (evals e1) == (B True) && (evals e2) == (B True) = evals(Mul (eval1 e1) (eval1 e2))
        | (evals e1) == (B True) && (evals e2) == (B False) = (Mul (eval1 e1) e2)
        | (evals e1) == (B False) && (evals e2) == (B True) = (Mul e1 (eval1 e2))
        | otherwise = (Mul e1 e2)
    evalsAux (Succ (I n)) = I (n + 1)
    evalsAux (Succ (B b)) = Succ (B b)
    evalsAux (Succ e1)
        | (evals e1) == (B True) = evalsAux(Succ (eval1 e1))
        | otherwise = (Succ e1) 
    evalsAux (Pred (I n)) = I (n - 1) 
    evalsAux (Pred (B b)) = Pred (B b)
    evalsAux (Pred e1)
        | (evals e1) == (B True) = evalsAux(Pred (eval1 e1))
        | otherwise = (Pred e1) 
    evalsAux (Not (I n)) = (Not (I n))
    evalsAux (Not e1)
        | (evals e1) == (B True) = evalsAux(Not (eval1 e1))
        | otherwise = (Not e1)
    evalsAux (And (B b) (B v)) = B (b && v)
    evalsAux (And (I n) (B b)) = And (I n) (B b)
    evalsAux (And (B b) (I n)) = And (B b) (I n)
    evalsAux (And (I n) (I m)) = And (I n) (I m)
    evalsAux (And e1 e2)
        | (evals e1) == (B True) && (evals e2) == (B True) = evals(And (eval1 e1) (eval1 e2))
        | (evals e1) == (B True) && (evals e2) == (B False) = (And (eval1 e1) e2)
        | (evals e1) == (B False) && (evals e2) == (B True) = (And e1 (eval1 e2))
        | otherwise = (And e1 e2)
    evalsAux (Or (B b) (B v)) = B (b || v)
    evalsAux (Or (I n) (B b)) = Or (I n) (B b)
    evalsAux (Or (B b) (I n)) = Or (B b) (I n)
    evalsAux (Or (I n) (I m)) = Or (I n) (I m)
    evalsAux (Or e1 e2)
        | (evals e1) == (B True) && (evals e2) == (B True) = evals(Or (eval1 e1) (eval1 e2))
        | (evals e1) == (B True) && (evals e2) == (B False) = (Or (eval1 e1) e2)
        | (evals e1) == (B False) && (evals e2) == (B True) = (Or e1 (eval1 e2))
        | otherwise = (Or e1 e2)
    evalsAux (Lt (I n) (I m)) = B (n < m)
    evalsAux (Lt (I n) (B b)) = Lt (I n) (B b)
    evalsAux (Lt (B b) (I m)) = Lt (B b) (I m)
    evalsAux (Lt (B b) (B v)) = Lt (B b) (B v)
    evalsAux (Lt e1 e2)
        | (evals e1) == (B True) && (evals e2) == (B True) = evals(Lt (eval1 e1) (eval1 e2))
        | (evals e1) == (B True) && (evals e2) == (B False) = (Lt (eval1 e1) e2)
        | (evals e1) == (B False) && (evals e2) == (B True) = (Lt e1 (eval1 e2))
        | otherwise = (Lt e1 e2) 
    evalsAux (Gt (I n) (I m)) = B (n > m)
    evalsAux (Gt (I n) (B b)) = Gt (I n) (B b)
    evalsAux (Gt (B b) (I m)) = Gt (B b) (I m)
    evalsAux (Gt (B b) (B v)) = Gt (B b) (B v)
    evalsAux (Gt e1 e2)
        | (evals e1) == (B True) && (evals e2) == (B True) = evals(Gt (eval1 e1) (eval1 e2))
        | (evals e1) == (B True) && (evals e2) == (B False) = (Gt (eval1 e1) e2)
        | (evals e1) == (B False) && (evals e2) == (B True) = (Gt e1 (eval1 e2))
        | otherwise = (Gt e1 e2)
    evalsAux (Eq (I n) (I m)) = B (n == m)
    evalsAux (Eq (I n) (B b)) = Eq (I n) (B b)
    evalsAux (Eq (B b) (I m)) = Eq (B b) (I m)
    evalsAux (Eq (B b) (B v)) = Eq (B b) (B v)
    evalsAux (Eq e1 e2)
        | (evals e1) == (B True) && (evals e2) == (B True) = evals(Eq (eval1 e1) (eval1 e2))
        | (evals e1) == (B True) && (evals e2) == (B False) = (Eq (eval1 e1) e2)
        | (evals e1) == (B False) && (evals e2) == (B True) = (Eq e1 (eval1 e2))
        | otherwise = (Eq e1 e2)
    evalsAux (If e1 e2 e3) 
        | evalsAux(eval1 e1) == (B True) = evalsAux (eval1 e2)
        | evalsAux(eval1 e1) == (B False) = evalsAux (eval1 e3) 
        | otherwise = (If e1 e2 e3)
    evalsAux (Let x e1 e2) = evalsAux (eval1 (subst e2 (x, e1))) 
    evalsAux _ = (B False)


    evalsAux2 :: Expr -> Expr
    evalsAux2 (I n) = (B True)
    evalsAux2 (B b) = (B True)
    evalsAux2 (V x) = (B False)
    evalsAux2 (Add (B n) (B m)) = (B False)
    evalsAux2 (Add (I n) (B m)) = (B False)
    evalsAux2 (Add (B n) (I m)) = (B False)
    evalsAux2 (Add (I n) (I m)) = (B True)
    evalsAux2 (Add e1 e2) = evalsAux(eval1 (Add e1 e2))
    evalsAux2 (Mul (B n) (B m)) = (B False)
    evalsAux2 (Mul (I n) (B m)) = (B False)
    evalsAux2 (Mul (B n) (I m)) = (B False)
    evalsAux2 (Mul (I n) (I m)) = (B True)
    evalsAux2 (Mul e1 e2) = evalsAux(eval1 (Mul e1 e2))
    evalsAux2 (Succ e) = evalsAux2(evalsAux(Succ e))
    evalsAux2 (Pred e) = evalsAux2(evalsAux(Pred e))
    evalsAux2 (Not e) = evalsAux2(evalsAux(Not e))
    evalsAux2 (Or (B n) (B m)) = (B False)
    evalsAux2 (Or (I n) (B m)) = (B False)
    evalsAux2 (Or (B n) (I m)) = (B False)
    evalsAux2 (Or (I n) (I m)) = (B True)
    evalsAux2 (Or e1 e2) = evalsAux(eval1 (Or e1 e2))
    evalsAux2 (And (B n) (B m)) = (B False)
    evalsAux2 (And (I n) (B m)) = (B False)
    evalsAux2 (And (B n) (I m)) = (B False)
    evalsAux2 (And (I n) (I m)) = (B True)
    evalsAux2 (And e1 e2) = evalsAux(eval1 (And e1 e2))
    evalsAux2 (Lt (B n) (B m)) = (B False)
    evalsAux2 (Lt (I n) (B m)) = (B False)
    evalsAux2 (Lt (B n) (I m)) = (B False)
    evalsAux2 (Lt (I n) (I m)) = (B True)
    evalsAux2 (Lt e1 e2) = evalsAux(eval1 (Lt e1 e2))
    evalsAux2 (Gt (B n) (B m)) = (B False)
    evalsAux2 (Gt (I n) (B m)) = (B False)
    evalsAux2 (Gt (B n) (I m)) = (B False)
    evalsAux2 (Gt (I n) (I m)) = (B True)
    evalsAux2 (Gt e1 e2) = evalsAux(eval1 (Gt e1 e2))
    evalsAux2 (Eq (I n) (I m)) = (B True)
    evalsAux2 (Eq (I n) (B m)) = (B False)
    evalsAux2 (Eq (B n) (I m)) = (B False)
    evalsAux2 (Eq (B n) (B m)) = (B False)
    evalsAux2 (Eq e1 e2) = evalsAux(eval1 (Eq e1 e2))
    evalsAux2 (If e1 e2 e3) = (if (evalsAux2(evalsAux e1) == (B True)) then evalsAux (eval1 e2) else evalsAux2 (eval1 e3))
    evalsAux2 (Let x e1 e2) = evalsAux (eval1 (subst e2 (x, e1)))
    evalsAux2 _ = (B False)


    evals :: Expr -> Expr
    evals e = eval1 (evalsAux2 e)

    {- Finción que se encarga de verificar si una expresión es un valor o una
       una expresión bloqueada-}
    evale :: Expr -> Expr
    evale (I n) = (B True)
    evale (B b) = (B True)
    evale (V x) = (B False)
    evale (Add (I n) (I m)) = (B True)
    evale (Add (I n) (B b)) = (B False)
    evale (Add (B b) (I m)) = (B False)
    evale (Add (B b) (B v)) = (B False)
    evale (Mul e1 e2) = evale(evals (Mul e1 e2))
    evale (Mul (I n) (I m)) = (B True)
    evale (Mul (I n) (B b)) = (B False)
    evale (Mul (B b) (I m)) = (B False)
    evale (Mul (B b) (B v)) = (B False)
    evale (Mul e1 e2) = evale(evals (Mul e1 e2))
    evale (Succ e) = evale(evals (Succ e))
    evale (Pred e) = evale(evals (Pred e))
    evale (Not e) = evale(evals (Not e))
    evale (And (B b) (B v)) = (B True)
    evale (And (I n) (B b)) = (B False)
    evale (And (B b) (I m)) = (B False)
    evale (And (I n) (I m)) = (B False)
    evale (And e1 e2) = evale(evals (And e1 e2))
    evale (Or (B b) (B v)) = (B True)
    evale (Or (I n) (B b)) = (B False)
    evale (Or (B b) (I m)) = (B False)
    evale (Or (I n) (I m)) = (B False)
    evale (Or e1 e2) = evale(evals (Or e1 e2))
    evale (Lt (I n) (I m)) = (B True)
    evale (Lt (I n) (B b)) = (B False)
    evale (Lt (B b) (I m)) = (B False)
    evale (Lt (B b) (B v)) = (B False)
    evale (Lt e1 e2) = evale(evals(Lt e1 e2))
    evale (Gt (I n) (I m)) = (B True)
    evale (Gt (I n) (B b)) = (B False)
    evale (Gt (B b) (I m)) = (B False)
    evale (Gt (B b) (B v)) = (B False)
    evale (Gt e1 e2) = evale(evals(Gt e1 e2))
    evale (Eq (I n) (I m)) = (B True)
    evale (Eq (I n) (B b)) = (B False)
    evale (Eq (B b) (I m)) = (B False)
    evale (Eq (B b) (B v)) = (B False)
    evale (Eq e1 e2) = evale (evals(Eq e1 e2))
    evale (If e1 e2 e3)
    	| ((evals e1) == (B True)) = evale (evals e2) 
    	| ((evals e1) == (B False)) = evale (evals e3)
    	| otherwise = (If e1 e2 e3)
    evale (Let x e1 e2) = evale (evals (subst e2 (x, e1)))	
    evale _ = (B False)
    
    -- Tipo de dato para identificar números y booleanos
    data Type = Integer | Boolean deriving(Eq)
    
    -- Sinónimo 
    type Decl = (Identifier, Type)
    
    -- Sinónimo
    type TypCtxt = [Decl]

    {- Verifica el tipado de un programa -} 
    vt :: TypCtxt -> Expr -> Type -> Bool
    vt [(x, Integer)] (I n) Integer = True
    vt [(x, Boolean)] (B b) Boolean = True
    vt c (V x) t = elem (x, t) c
    vt [(x, Integer)] (Add (B b) (I n)) Integer = False
    vt [(x, Integer)] (Add (I n) (I m)) Integer = True
    vt [(x, Integer)]  (Add (I n) (B b)) Integer = False
    vt [(x, Integer)]  (Add (B b) (B v)) Integer = False
    vt c (Add e1 e2) t = if t == Integer then (vt c e1 t)  && (vt c e2 t) else False
    vt [(x, Integer)] (Mul (I n) (I m)) Integer = True
    vt [(x, Integer)]  (Mul (B b) (I n)) Integer = False
    vt [(x, Integer)]  (Mul (I n) (B b)) Integer = False
    vt [(x, Integer)]  (Mul (B b) (B v)) Integer = False
    vt c (Mul e1 e2) t = if t == Integer then (vt c e1 t)  && (vt c e2 t) else False
    vt [(x, Integer)] (Succ (I n)) Integer = True
    vt [(x, Integer)]  (Succ (B b)) Integer = False
    vt c (Succ e) t = if t == Integer then (vt c e t) else False
    vt [(x, Integer)] (Pred (I n)) Integer = True
    vt [(x, Integer)]  (Pred (B b)) Integer = False
    vt c (Pred e) t = if t == Integer then (vt c e t) else False
    vt [(x, Boolean)] (Not (B b)) Boolean = True
    vt [(x, Boolean)] (Not (I n)) Boolean = False 
    vt c (Not e) t = if t == Boolean then (vt c e t) else False
    vt [(x, Boolean)] (And (B b) (B v)) Boolean = True
    vt [(x, Boolean)] (And (I n) (B b)) Boolean = False
    vt [(x, Boolean)] (And (B b) (I n)) Boolean = False
    vt [(x, Boolean)] (And (I b) (I v)) Boolean = False
    vt c (And e1 e2) t = if t == Boolean then (vt c e1 t)  && (vt c e2 t) else False
    vt [(x, Boolean)] (Or (B b) (B v)) Boolean = True
    vt [(x, Boolean)] (Or (I n) (B b)) Boolean = False
    vt [(x, Boolean)] (Or (B b) (I n)) Boolean = False
    vt [(x, Boolean)] (Or (I n) (I m)) Boolean = False
    vt c (Or e1 e2) t = if t == Boolean then (vt c e1 t)  && (vt c e2 t) else False
    vt [(x, Boolean)] (Lt (I n) (I m)) Boolean = True
    vt [(x, Boolean)] (Lt (I n) (B b)) Boolean = False
    vt [(x, Boolean)] (Lt (B b) (I n)) Boolean = False
    vt [(x, Boolean)] (Lt (B b) (B v)) Boolean = False
    vt c (Lt e1 e2) t = if t == Boolean then (vt c e1 t)  && (vt c e2 t) else False
    vt [(x, Boolean)] (Gt (I n) (I m)) Boolean = True
    vt [(x, Boolean)] (Gt (I n) (B b)) Boolean = False
    vt [(x, Boolean)] (Gt (B b) (I n)) Boolean = False
    vt [(x, Boolean)] (Gt (B b) (B v)) Boolean = False
    vt c (Gt e1 e2) t = if t == Boolean then (vt c e1 t)  && (vt c e2 t) else False
    vt [(x, Boolean)] (Eq (I n) (I m)) Boolean = True
    vt [(x, Boolean)] (Eq (I n) (B b)) Boolean = False
    vt [(x, Boolean)] (Eq (B b) (I n)) Boolean = False
    vt [(x, Boolean)] (Eq (B b) (B v)) Boolean = False
    vt c (Eq e1 e2) t = if t == Boolean then (vt c e1 t)  && (vt c e2 t) else False
    vt c (If e1 e2 e3) t = vt c e1 Boolean && vt c e2 t && vt c e3 t
    vt _ _ _ = False

    {- Función que se encarga de verificar el tipado de un programa
       y devuelve la evalucíon en casi que de sea verdadero -}
    eval :: Expr -> Type -> Expr
    eval (I n) Integer = error ":("
    eval (B b) Boolean = error ":("
    eval (Add (I n) (I m)) Integer = I (n + m)
    eval (Add (I n) (B b)) Integer = error "El tipo no corresponde" 
    eval (Add (B b) (I n)) Integer = error "El tipo no corresponde" 
    eval (Add (B b) (B v)) Integer = error "El tipo no corresponde" 
    eval (Add e1 e2) t = if t == Integer then evals(Add e1 e2) else error "El tipo no corresponde" 
    eval (Mul (I n) (I m)) Integer = I (n * m) 
    eval (Mul (I n) (B b)) Integer = error "El tipo no corresponde" 
    eval (Mul (B b) (I n)) Integer = error "El tipo no corresponde" 
    eval (Mul (B b) (B v)) Integer = error "El tipo no corresponde" 
    eval (Mul e1 e2) t = if t == Integer then evals(Mul e1 e2) else error "El tipo no corresponde" 
    eval (Succ (I n)) Integer = I (n + 1)
    eval (Succ (B b)) Integer = error "El tipo no corresponde" 
    eval (Succ e) t = if t == Integer then evals(Succ e) else error "El tipo no corresponde" 
    eval (Pred (I n)) Integer = I (n - 1)
    eval (Pred (B b)) Integer = error "El tipo no corresponde" 
    eval (Pred e) t = if t == Integer then evals(Pred e) else error "El tipo no corresponde" 
    eval (Not (B b)) Boolean = B (not b)
    eval (Not (I n)) Boolean = error "El tipo no corresponde" 
    eval (Not e) t = if t == Boolean then evals(Not e) else error "El tipo no corresponde" 
    eval (And (B b) (B v)) Boolean = B (b && v)
    eval (And (I n) (B b)) Boolean = error "El tipo no corresponde" 
    eval (And (B b) (I n)) Boolean = error "El tipo no corresponde" 
    eval (And (I b) (I v)) Boolean = error "El tipo no corresponde" 
    eval (And e1 e2) t = if t == Boolean then evals(And e1 e2) else error "El tipo no corresponde"
    eval (Or (B n) (B m)) Boolean = B (n || m) 
    eval (Or (I n) (B b)) Boolean = error "El tipo no corresponde" 
    eval (Or (B b) (I n)) Boolean = error "El tipo no corresponde" 
    eval (Or (I b) (I v)) Boolean = error "El tipo no corresponde" 
    eval (Or e1 e2) t = if t == Boolean then evals(Or e1 e2) else error "El tipo no corresponde"
    eval (Lt (I n) (I m)) Boolean = B (n < m)
    eval (Lt (I n) (B b)) Boolean = error "El tipo no corresponde" 
    eval (Lt (B b) (I n)) Boolean = error "El tipo no corresponde" 
    eval (Lt (B b) (B v)) Boolean = error "El tipo no corresponde"  
    eval (Lt e1 e2) t = if t == Boolean then evals(Lt e1 e2) else error "El tipo no corresponde"
    eval (Gt (I n) (I m)) Boolean = B (n > m)
    eval (Gt (I n) (B b)) Boolean = error "El tipo no corresponde" 
    eval (Gt (B b) (I n)) Boolean = error "El tipo no corresponde" 
    eval (Gt (B b) (B v)) Boolean = error "El tipo no corresponde"  
    eval (Gt e1 e2) t = if t == Boolean then evals(Gt e1 e2) else error "El tipo no corresponde"
    eval (Eq (I n) (I m)) Boolean = B (n == m)
    eval (Eq (I n) (B b)) Boolean = error "El tipo no corresponde" 
    eval (Eq (B b) (I n)) Boolean = error "El tipo no corresponde" 
    eval (Eq (B b) (B v)) Boolean = error "El tipo no corresponde"  
    eval (Eq e1 e2) t = if t == Boolean then evals(Eq e1 e2) else error "El tipo no corresponde"
    eval (If e1 e2 e3) t = eval(evals(If e1 e2 e2)) t
    eval (Let x e1 e2) t = eval(evals(Let x e1 e2)) t
    eval _ _ = error "El tipo no corresponde"
