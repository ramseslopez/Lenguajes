module BAE.Semantic where
   
   import BAE.Sintax
    

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
   eval1 (Let x (V v) e2) = subst e2 (x, (V v))
   eval1 (Let x e1 e2) = Let x (eval1 e1) e2

   evals :: Expr -> Expr
   evals (I n) = I n
   evals (B b) = B b
   evals (V x) = V x
   evals (Add (I n) (I m)) = I (n + m)
   evals (Add (I n) (B b)) = Add (I n) (B b)
   evals (Add (B v) (I n)) = Add (B v) (I n)
   evals (Add e1 e2) = evals(eval1 (Add e1 e2))
   evals (Mul (I n) (I m)) = I (n * m)
   evals (Mul (I n) (B b)) = Mul (I n) (B b)
   evals (Mul (B v) (I n)) = Mul (B v) (I n)
   evals (Mul e1 e2) = evals(eval1 (Mul e1 e2))
   evals (Succ e1) = evals(eval1 (Succ e1))
   evals (Pred e1) = evals(eval1 (Pred e1))
   evals (Not e1) = evals(eval1 (Not e1))
   evals (And e1 e2) = evals(eval1 (And e1 e2))
   evals (Or e1 e2) = evals(eval1 (Or e1 e2))
   evals (Lt e1 e2) = evals(eval1 (Lt e1 e2))
   evals (Gt e1 e2) = evals(eval1 (Gt e1 e2))
   evals (Eq e1 e2) = evals(eval1 (Eq e1 e2))
   evals (If e1 e2 e3) = evals(eval1 (If e1 e2 e3))
   evals (Let x e1 e2) = evals(eval1 (Let x e1 e2)) 

    {- Función que se encarga de verificar si una expresión es un valor o una
       una expresión bloqueada-}
   evale :: Expr -> Expr
   evale (I n) = error "Error"
   evale (B v) = error "Error"
   evale (V x) = error "Error"
   evale (Add e1 e2) = error "Error"
   evale (Mul e1 e2) = error "Error"
   evale (Succ e1) = error "Error"
   evale (Pred e1) = error "Error"
   evale (Not e1) = error "Error"
   evale (Or e1 e2) = error "Error"
   evale (Lt e1 e2) = error "Error"
   evale (Gt e1 e2) = error "Error"
   evale (Eq e1 e2) = error "Error"
   evale (If e1 e2 e3) = error "Error"
   evale (Let x e1 e2) = error "Error"
   
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
   vt [(x, Integer)]  (Mul (B b) (I n)) Integer  = False
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
   vt c (Let x e1 e2) t = if (vt c e1 Integer) then vt (union [(x, Integer)] (c \\ [(x, Integer), (x, Boolean)])) e2 t else if (vt (cons [(x, Boolean)] c) e2 t) then (vt (union [(x, Boolean)] (c \\ [(x, Integer), (x, Boolean)])) e2 t) else error "inalcanzable"
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
   eval (Add (I n) (B b)) Boolean = error "El tipo no corresponde" 
   eval (Add (B b) (I n)) Boolean = error "El tipo no corresponde" 
   eval (Add (I b) (I v)) Boolean = error "El tipo no corresponde" 
   eval (And e1 e2) t = if t == Boolean then evals(And e1 e2) else error "El tipo no corresponde"
   eval (Or (B n) (B m)) Integer = B (n || m) 
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
