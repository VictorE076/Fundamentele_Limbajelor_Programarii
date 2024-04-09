import Data.Char

newtype Parser a = Parser { parse :: String -> [(a,String)] }

---
-- data Parser a = Parser (String -> [(a, String)])

-- parse :: Parser a -> (String -> String -> [(a, String)])
-- parse (Parser p) = pa

-- parse expr "asdsdf"
---

item :: Parser Char
item = Parser (\cs -> case cs of
                "" -> []
                (c:cs) -> [(c,cs)])

instance Monad Parser where
    return a = Parser (\cs -> [(a,cs)])
    p >>= f = Parser (\cs -> concat (map (\(a, cs') -> (parse (f a) cs')) (parse p cs)))

instance Applicative Parser where
    pure = return
    mf <*> ma = do
        f <- mf
        va <- ma
        return (f va)    

instance Functor Parser where              
    fmap f ma = pure f <*> ma   
  
{-
instance Functor Parser where              
    fmap g p = Parser (\cs -> map (\(a,cs') -> (g a, cs')) (parse p cs))

instance Applicative Parser where
    pure a = Parser (\cs -> [(a, cs)])
    pg <*> pa = Parser (\cs -> concat (map (\(g, cs') -> (parse (fmap g pa) cs')) (parse pg cs)))

instance Monad Parser where
    p >>= f = Parser (\cs -> concat (map (\(a, cs') -> (parse (f a) cs')) (parse p cs)))
-}

zero :: Parser a
zero = Parser (const [])

psum :: Parser a -> Parser a -> Parser a
psum p q = Parser (\cs -> (parse p cs) ++ (parse q cs))

(<|>) :: Parser a -> Parser a -> Parser a
p <|> q = Parser (\cs -> case parse (psum p q) cs of
                                [] -> []
                                (x:xs) -> [x])

dpsum0 :: Parser [a] -> Parser [a]
dpsum0 p = p <|> (return [])

sat :: (Char -> Bool) -> Parser Char
sat p = do
            c <- item
            if p c then return c else zero

char :: Char -> Parser Char
char c = sat (c ==)

string :: String -> Parser String
string [] = return []
string (c:cs) = do
                    pc <- char c
                    prest <- string cs
                    return (pc : prest)

many0 :: Parser a -> Parser [a]
many0 p = dpsum0 (many1 p)

many1 :: Parser a -> Parser [a]
many1 p = do 
    a <- p -- a = tip "a", despachetat
    aa <- many0 p -- aa = tip "[a]", despachetat
    return (a : aa) -- Impachetam inapoi lista "a : aa" in tipul "Parser [a]"

spaces :: Parser String -- !!! Functie fara parametrii care returneaza un "Parser String"
spaces = many0 (sat isSpace)

token :: Parser a -> Parser a
token p = do
            spaces
            x <- p
            spaces
            return x

symbol :: String -> Parser String
symbol symb = token (string symb)

sepBy0 :: Parser a1 -> Parser a2 -> Parser [a1]
p `sepBy0` sep = dpsum0 (p `sepBy1` sep)

sepBy1 :: Parser a1 -> Parser a2 -> Parser [a1]
p `sepBy1` sep = do
                    a <- p -- a <- Parser a
                    as <- many0 (do
                                    sep
                                    p) -- [a] <- Parser [a]
                    return (a:as) -- [a] Impachetat = Parser [a]

look :: Parser (Maybe Char)
look = Parser (\cs -> case cs of
      [] -> [(Nothing, [])]
      (c:cs') -> [(Just c, c:cs')]
    )

takeUntil :: Char -> Parser [Char]
takeUntil stop = consumeRest "" stop
    where consumeRest acc stop = do
                                    l <- look
                                    if l == Just stop then return [] else do
                                                                            c <- item
                                                                            cs <- consumeRest (acc ++ [c]) stop
                                                                            return (c:cs)

chainl1 :: Parser t -> Parser (t -> t -> t) -> Parser t
p `chainl1` op = do
                    x <- p
                    rest x
                 where rest x = (do
                                    f <- op
                                    y <- p
                                    rest (f x y)
                                ) <|> return x

digit :: Parser Int
digit = do
            d <- sat isDigit
            return (digitToInt d)

integer :: Parser Int
integer = do
              spaces
              d <- digitToInt <$> sat isDigit
              if d == 0 
                then 
                  return 0 
                else 
                  do
                    ds <- many0 digit
                    return (asInt (d:ds)) -- !!! Un "int" (suma de elemente din lista) impachetat inapoi in "Parser Int"
          where asInt ds = sum [d * (10^p) | (d, p) <- zip (reverse ds) [0..] ]


-- 2.:

number :: Parser Double
number = withDecimalPt <|> withoutDecimalPt
  where
    withoutDecimalPt = fromIntegral <$> integer
    withDecimalPt = do
                      wholePart <- withoutDecimalPt
                      char '.'
                      fractionalPart <- fmap asFracPt (many0 digit)
                      return (wholePart + fractionalPart)
    asFracPt ds = sum [fromIntegral d * (10 ** (-p)) | (d, p) <- zip ds [1..]]

{-
addop :: Parser (Double -> Double -> Double)
addop = add <|> sub
  where add = do
                symbol "+"
                return (+)
        sub = do
                symbol "-"
                return (-)

mulop :: Parser (Double -> Double -> Double)
mulop = mul <|> div
  where mul = do
                symbol "*"
                return (*)
        div = do
                symbol "/"
                return (/)

factor :: Parser Exp
factor = negativeFactor <|> parensExpr <|> number
  where
    negativeFactor = do
                        symbol "-"
                        negate <$> factor
    parensExpr = do
                    symbol "("
                    x <- expr
                    symbol ")"
                    return x
                    
term :: Parser Double
term = factor `chainl1` mulop


-- 1.:
-- !!! Parser-ul final (folosit si-n terminal)

expr :: Parser Double
expr = term `chainl1` addop

-}

--1. Testati parser-ul de mai sus

--2. Creati un tip de date abstract (inductiv) pt expresii aritmetice si modificati parser-ul astfel incat el sa returneze o asemenea expresie


-- 2.:

data Exp = Num Double | Add Exp Exp | Mult Exp Exp | Div Exp Exp | Sub Exp Exp | Neg Exp | Paren Exp 
                deriving Show 

{-
number2 :: Parser Double
number2 = withDecimalPt <|> withoutDecimalPt
  where
    withoutDecimalPt = fromIntegral <$> integer
    withDecimalPt = do
                      wholePart <- withoutDecimalPt
                      char '.'
                      fractionalPart <- fmap asFracPt (many0 digit)
                      return (wholePart + fractionalPart)
    asFracPt ds = sum [fromIntegral d * (10 ** (-p)) | (d, p) <- zip ds [1..]]
-}

-- 1+2 -> 3
-- Add (Num 1) (Num 2) -- !!! Parsare 

addop :: Parser (Exp -> Exp -> Exp)
addop = add <|> sub
  where add = do
                symbol "+"
                return (Add)
        sub = do
                symbol "-"
                return (Sub)

mulop :: Parser (Exp -> Exp -> Exp)
mulop = mul <|> div
  where mul = do
                symbol "*"
                return (Mult)
        div = do
                symbol "/"
                return (Div)

factor :: Parser Exp
factor = negativeFactor <|> parensExpr <|> fmap Num number
  where
    negativeFactor = do
                        symbol "-"
                        Neg <$> factor
    parensExpr = do
                    symbol "("
                    x <- expr
                    symbol ")"
                    return (Paren x)
                    
term :: Parser Exp
term = factor `chainl1` mulop


-- 1.:
-- !!! Parser-ul final (folosit si-n terminal)

expr :: Parser Exp
expr = term `chainl1` addop


-- !!! Exemplu:
 
-- ghci> parse expr "-(1 + 2) * 5"
-- [(Mult (Neg (Paren (Add (Num 1.0) (Num 2.0)))) (Num 5.0),"")] 