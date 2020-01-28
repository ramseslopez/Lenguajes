module Practica1 where

  -- Práctica 1 : Intérprete de expresiones aritmético-booleanas


  -- Tipo de dato para definir las instrucciones
  data Instruction = I Int | B Bool
                    | ADD | AND | OR | DIV | EQQ | EXEC
                    | GET | Gt | Lt | POW | MAX | MIN | FACT | MUL
                    | NOT | POP | REM | SEL | SUB
                    | SWAP | ES [Instruction] deriving (Eq, Show)

  -- Sinónimo Stack para una lista de instrucciones
  type Stack = [Instruction]

  -- Sinónimo Program para una lista de instrucciones
  type Program = [Instruction]

  -- Función que se encarga de realizar todas las operaciones aritméticas
  -- haciendo uso de instrucciones.
  arithOperation :: Instruction -> Instruction -> Instruction -> Instruction
  arithOperation (I n) (I m) ADD = (I (n + m))
  arithOperation (I n) (I m) SUB = (I (m - n))
  arithOperation (I n) (I m) MUL = (I (n * m))
  arithOperation (I n) (I m) DIV = if n /= 0 then (I (div n m))
                                    else
                                      error "No se puede realizar la operacion"
  arithOperation (I n) (I m) REM = if n /= 0 then (I (mod n m))
                                    else
                                      error "No se puede realizar la operacion"

  -- Función que se encarga de mostrar la valuación del operador binario AND
  -- a modo de instrucción
  bboolOperation :: Instruction -> Instruction -> Instruction -> Instruction
  bboolOperation (B n) (B m) AND = (B (n && m))

  -- Función que se encarga de mostrar la valuación del operador unario NOT
  -- a modo de instrucción
  uboolOperation :: Instruction -> Instruction -> Instruction
  uboolOperation (B n) NOT = (B (not n))

  -- Función que se encarga de mostrar el resultado luego de comparar si dos
  -- números son iguales o uno es mayor o menor que otro.
  relOperation :: Instruction -> Instruction -> Instruction -> Instruction
  relOperation (I n) (I m) EQQ  = if n == m then (B True)
                                    else
                                      (B False)
  relOperation (I n) (I m) Gt   = if m > n then (B True)
                                    else
                                      (B False)
  relOperation (I n) (I m) Lt   = if m < n then (B True)
                                    else
                                      (B False)

  -- Función que se encarga de realizar las operaciones de una pila usando
  -- las instrucciones definidas
  stackOperation :: Stack -> Instruction -> Stack
  stackOperation [] (I n)       = [I n]
  stackOperation [] (B b)       = [B b]
  stackOperation (x:xs) POP     = xs
  stackOperation (x:y:xs) SWAP  = (y:x:xs)
  stackOperation (x:y:z:xs) SEL = if z == (B False) then (x:xs)
                                    else
                                      (y:xs)
  stackOperation (x:xs) (ES ys) = (ES ys):(x:xs)
  stackOperation (x:xs) GET     = if x == (I 0) then (x:xs)
                                    else
                                      stackOperation (x:xs) POP

  -- Función que se encarga de meter al tope de la pila la lista de
  -- de instrucciones ejecutables
  execOperation :: [Instruction] -> Stack -> Instruction -> ([Instruction], Stack)
  execOperation xs [] EXEC            = error "La accion no puede ser procesada"
  execOperation xs ((ES ys):zs) EXEC  = (ys ++ xs, zs)

  -- Función que se encarga de de realizar la evaluación de un programa y una
  -- una lista de instrucciones
  executeProgram :: Program -> Stack -> Stack
  executeProgram [] []  = error "La operacion no es posible"
  executeProgram [] p = p
  executeProgram ((ADD):xs) (a:b:p) = executeProgram xs ((arithOperation a b ADD):p)
  executeProgram ((SUB):xs) (a:b:p) = executeProgram xs ((arithOperation a b SUB):p)
  executeProgram ((MUL):xs) (a:b:p) = executeProgram xs ((arithOperation a b MUL):p)
  executeProgram ((DIV):xs) (a:b:p) = executeProgram xs ((arithOperation a b DIV):p)
  executeProgram ((REM):xs) (a:b:p) = executeProgram xs ((arithOperation a b REM):p)
  executeProgram ((EQQ):xs) (a:b:p) = executeProgram xs ((arithOperation a b EQQ):p)
  executeProgram ((Gt):xs) (a:b:p)  = executeProgram xs ((arithOperation a b Gt):p)
  executeProgram ((Lt):xs) (a:b:p)  = executeProgram xs ((arithOperation a b Lt):p)
  executeProgram ((AND):xs) (a:b:p) = executeProgram xs ((bboolOperation a b AND):p)
  executeProgram ((NOT):xs) (a:p)   = executeProgram xs ((uboolOperation a NOT):p)
  executeProgram ((I n):xs) p       = executeProgram xs (stackOperation p (I n))
  executeProgram ((B b):xs) p       = executeProgram xs (stackOperation p (B b))
  executeProgram ((POP):xs) p       = executeProgram xs (stackOperation p POP)
  executeProgram ((SWAP):xs) p      = executeProgram xs (stackOperation p SWAP)
  executeProgram ((SEL):xs) p       = executeProgram xs (stackOperation p SEL)
  executeProgram ((ES ys):xs) p     = executeProgram xs (stackOperation p (ES ys))
  executeProgram ((GET):xs) p       = executeProgram xs (stackOperation p GET)


  -- Tipo de dato para definir las expresiones requeridas
  data Expr = N Int | T | F
              | Succ Expr | Pred Expr
              | Expr :+ Expr | Expr :- Expr
              | Expr :* Expr | Expr :/ Expr | Expr :% Expr
              | Not Expr | Expr :& Expr | Expr :| Expr
              | Expr :> Expr | Expr :< Expr | Expr := Expr
              | Expr :^ Expr
              | Max Expr Expr | Min Expr Expr
              | Fact Expr deriving (Eq, Show)

  -- Función que se encarga de traducir una istrucción a un programa
  compile:: Expr -> Program
  compile T             = [B True]
  compile F             = [B False]
  compile (N n)         = [I n]
  compile (Succ (N n))  = [I n] ++ [I 1] ++ [ADD]
  compile (Pred (N n))  = if n <= 0 then error "No es posible hacer la operación"
                            else
                              [I n] ++ [I 1] ++ [SUB]
  compile (n :+ m)      = compile n ++ compile m ++ [ADD]
  compile (n :- m)      = compile n ++ compile m ++ [SUB]
  compile (n :* m)      = compile n ++ compile m ++ [MUL]
  compile (n :/ m)      = compile n ++ compile m ++ [DIV]
  compile (n :% m)      = compile n ++ compile m ++ [REM]
  compile (Not n)       = compile n ++ [NOT]
  compile (n :& m)      = compile n ++ compile m ++ [AND]
  compile (n :| m)      = compile n ++ compile m ++ [OR]
  compile (n :> m)      = compile n ++ compile m ++ [Gt]
  compile (n :< m)      = compile n ++ compile m ++ [Lt]
  compile (n := m)      = compile n ++ compile m ++ [EQQ]
  compile ((N n) :^ (N m))
  					| compile (N m) == [I 0] = [I 1]
  					| compile (N m) == [I 1] = compile (N n)
  					| (relOperation (head (compile (N m))) (I 1) Lt) == (B True) = (compile (N n)) ++ compile ((N n) :^ (N (m-1))) ++ [MUL]
  					| otherwise = error "La operacion no piede ser procesada"
  compile (Min n m) = compile n ++  compile m ++ [Lt] ++ compile n ++ compile m ++ [SEL]
  compile (Max n m) = compile n ++  compile m ++ [Gt] ++ compile n ++ compile m ++ [SEL]
  compile (Fact (N n))
  					| compile (N n) == [I 0] = [I 1]
  					| compile (N n) == [I 1] = [I 1]
  					| relOperation (head (compile (N n))) (I 1) Lt == (B True) = compile (N n) ++ compile (Fact (N (n-1))) ++ [MUL]
  					| otherwise = error "La operacion no puede ser procesada"

  -- Función que se encarga de traducir una expresión a una instrucción
  execute :: Expr -> Instruction
  execute T            = B True
  execute F            = B False
  execute (N n)        = I n
  execute (Succ n)     = arithOperation (execute n) (I 1) ADD
  execute (Pred n)     = arithOperation (execute n) (I 1) SUB
  execute (n :+ m)     = arithOperation (execute n) (execute m) ADD
  execute (n :- m)     = arithOperation (execute n) (execute m) SUB
  execute (n :* m)     = arithOperation (execute n) (execute m) MUL
  execute (n :/ m)     = arithOperation (execute n) (execute m) DIV
  execute (n :% m)     = arithOperation (execute n) (execute m) REM
  execute (Not n)      = uboolOperation (execute n) NOT
  execute (n :& m)     = bboolOperation (execute n) (execute m) AND
  execute (n :| m)     = bboolOperation (execute n) (execute m) OR
  execute (n :> m)     = bboolOperation (execute n) (execute m) Gt
  execute (n :< m)     = bboolOperation (execute n) (execute m) Lt
  execute (n := m)     = bboolOperation (execute n) (execute m) EQQ
  execute (n :^ m)     = arithOperation (execute n) (execute m) POW
  execute (Min n m)    = relOperation (execute n) (execute m) Lt
  execute (Max n m)    = relOperation (execute n) (execute m) Gt
  execute (Fact (N n)) = arithOperation (execute (N n)) (execute (N (n-1))) MUL
