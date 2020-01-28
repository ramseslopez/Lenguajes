module BAE.Memory where

    import Data.List
    import BAE.Sintax

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
