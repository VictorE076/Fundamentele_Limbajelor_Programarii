data Term = Variable String | FuncSym String [Term]
    deriving (Eq, Show)

-- returns all variables of a term
var :: Term -> [String]
var (Variable v) = [v]
var (FuncSym _ terms) = concatMap var terms

-- substitutes, in a term, a variable by another term
subst :: Term -> String -> Term -> Term
subst (Variable s1) s2 t2 = if s1 == s2 then t2 else (Variable s1)
subst (FuncSym sym terms) s t = FuncSym sym (map (\term -> subst term s t) terms)

data Equ = Equ Term Term
    deriving Show

data StepResult = FailureS | Stopped | SetS [Equ]
    deriving Show

step1 :: [Equ] -> StepResult
step1 [] = Stopped 
step1 ((Equ (FuncSym name1 subterms1) (FuncSym name2 subterms2)):eqs)
    | name1 == name2 = SetS (zipWith Equ subterms1 subterms2 ++ eqs) 
step1 (eq:eqs) = case (step1 eqs) of   
                    FailureS -> FailureS
                    Stopped -> Stopped
                    SetS newEqs -> SetS (eq : newEqs)


step2 :: [Equ] -> StepResult
step2 [] = Stopped 
step2 ((Equ (FuncSym name1 subterms1) (FuncSym name2 subterms2)):eqs)
    | name1 /= name2 = FailureS
    | length subterms1 /= length subterms2 = FailureS 
step2 (eq:eqs) = case (step2 eqs) of   
                    FailureS -> FailureS
                    Stopped -> Stopped
                    SetS newEqs -> SetS (eq : newEqs)

step3 :: [Equ] -> StepResult
step3 [] = Stopped  
step3 (eq:eqs) =
    case eq of
        Equ (Variable x) (Variable y)
            | x == y -> step3 eqs  
        _ -> case step3 eqs of
                FailureS -> FailureS  
                Stopped -> Stopped    
                SetS newEqs -> SetS (eq : newEqs)


step4 :: [Equ] -> StepResult
step4 [] = Stopped  
step4 ((Equ (Variable x) t):eqs)
    | containsVariable x t && t == Variable x = FailureS  
    | otherwise = step4 eqs  
  where
    containsVariable :: String -> Term -> Bool
    containsVariable var (Variable y) = var == y
    containsVariable var (FuncSym _ subterms) = any (containsVariable var) subterms
step4 (_:eqs) = step4 eqs

step5 :: [Equ] -> StepResult
step5 [] = Stopped  
step5 ((Equ (Variable x) t):eqs)
    | containsVariable x t && t == Variable x = FailureS  
    | otherwise = step5 eqs  
  where
    containsVariable :: String -> Term -> Bool
    containsVariable var (Variable y) = var == y
    containsVariable var (FuncSym _ subterms) = any (containsVariable var) subterms
step5 (_:eqs) = step5 eqs

-- candidates for "x=t" in step 6 of the algorithm
step6cand :: [Equ] -> [Equ]
step6cand eqs = concatMap replaceOccurrences eqs
  where
    replaceOccurrences (Equ (Variable x) t) =
      let eqsWithX = filter (\(Equ l _) -> l == Variable x) eqs
          remainingEqs = filter (\eq -> not (eq `elem` eqsWithX)) eqs
      in map (\(Equ l r) -> Equ (subst l x t) (subst r x t)) remainingEqs
    replaceOccurrences _ = []

-- substitutes in a list of equations a variable by a term EXCEPT for the equation "variable=term" (as used in step 6 of the algorithm)
substeq :: [Equ] -> String -> Term -> [Equ]
substeq [] _ _ = []
substeq ((Equ (Variable x) t) : es) var term =
    if x == var
        then (Equ (Variable x) t) : substeq es var term
        else (Equ (subst (Variable x) var term) (subst t var term)) : substeq es var term
substeq (_ : es) var term = substeq es var term

step6 :: [Equ] -> StepResult
step6 xs = case step6cand xs of 
        (Equ (Variable x) t) : _ -> SetS(substeq xs x t) 
        _ -> Stopped
                
onestep :: [Equ] -> StepResult
onestep es = case (step1 es) of
              SetS fs -> SetS fs
              Stopped -> case (step2 es) of
                          FailureS -> FailureS
                          Stopped -> case (step3 es) of
                                      SetS fs -> SetS fs
                                      Stopped -> case (step4 es) of
                                                  SetS fs -> SetS fs
                                                  Stopped -> case (step5 es) of
                                                              FailureS -> FailureS
                                                              Stopped ->  case (step6 es) of
                                                                           SetS fs -> SetS fs
                                                                           Stopped -> Stopped

data AllResult = Failure | Set [Equ]
    deriving Show

unify :: [Equ] -> AllResult
unify es = case (onestep es) of
                    Stopped -> Set es
                    FailureS -> Failure
                    SetS fs -> unify fs
                    
eqset1 = [Equ (Variable "z") (FuncSym "f" [Variable "x"]), Equ (FuncSym "f" [Variable "t"]) (Variable "y")]
         -- z=f(x), f(t)=y  --> should have z=f(x), y=f(t)

eqset2 = [Equ (FuncSym "f" [Variable "x", FuncSym "g" [Variable "y"]]) (FuncSym "f" [FuncSym "g" [Variable "z"], Variable "z"])]
         -- f(x,g(y))=f(g(z),z) --> should have x=g(g(y)), z=g(y)

eqset3 = [Equ (FuncSym "f" [Variable "x", FuncSym "g" [Variable "x"], FuncSym "b" []]) (FuncSym "f" [FuncSym "a" [], FuncSym "g" [Variable "z"], Variable "z"])]
          -- f(x,g(x),b)=f(a,g(z),z) --> should return failure