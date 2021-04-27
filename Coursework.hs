
--------------------------------------------
--                                        --
-- CM20256/CM50262 Functional Programming --
--                                        --
--         Coursework 2020/2021           --
--                                        --
--------------------------------------------


------------------------- Auxiliary functions

find :: (Show a,Eq a) => a -> [(a,b)] -> b
find x [] = error ("find: " ++ show x ++ " not found")
find x ((y,z):zs)
  | x == y    = z
  | otherwise = find x zs


merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys


------------------------- Lambda-terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq


instance Show Term where
  show = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = free n `minus` [x]
free (Apply  n m) = free n `merge` free m

------------------------- Types

infixr 5 :->

type Atom = String
data Type = At Atom | Type :-> Type
  deriving Eq

instance Show Type where
  show (At a)       = a
  show (At a :-> s) = a ++ " -> " ++ show s
  show    (t :-> s) = "(" ++ show t ++ ") -> " ++ show s


atoms :: [Atom]
atoms = map (:[]) ['a'..'z'] ++ [ a : show i | i <- [1..], a <- ['a'..'z'] ]

t1 :: Type
t1 = At "a" :-> At "b"

t2 :: Type
t2 = (At "c" :-> At "d") :-> At "e"

t3 :: Type
t3 = At "a" :-> At "c" :-> At "c"


------------------------- Assignment 1

occurs :: Atom -> Type -> Bool
-- atom
occurs a (At atom) = a == atom
  -- type -> type
occurs a (t1 :-> t2) = occurs a t1 || occurs a t2

findAtoms :: Type -> [Atom]
-- atom
findAtoms (At atom) = [atom]
-- type -> type
findAtoms (t1 :-> t2) = merge (findAtoms t1) (findAtoms t2)

------------------------- Type substitution

type Sub = (Atom,Type)

s1 :: Sub
-- replaces all the a with e
s1 = ("a", At "e")

s2 :: Sub
s2 = ("e", At "b" :-> At "c")

s3 :: Sub
s3 = ("c", At "a" :-> At "a")


------------------------- Assignment 2

sub :: Sub -> Type -> Type
-- atom
sub (atomToReplace, replacementAtom) (At atom) = if atom == atomToReplace then replacementAtom else At atom
-- type -> type
sub s (t1 :-> t2) = sub s t1 :-> sub s t2

subs :: [Sub] -> Type -> Type
-- non empty sub series
subs xs t = reverseSubs (reverse xs) t
  where 
    reverseSubs :: [Sub] -> Type -> Type
    -- empty sub series
    reverseSubs [] t = t
    -- non empty sub series
    reverseSubs (x : xs) t = reverseSubs xs (sub x t)



------------------------- Unification

type Upair = (Type,Type)
type State = ([Sub],[Upair])

u1 :: Upair
u1 = (t1,At "c")

u2 :: Upair
u2 = (At "a" :-> At "a",At "a" :-> At "c")

u3 :: Upair
u3 = (t1,t2)

u4 :: Upair
u4 = (t2,t3)

st1 :: State
st1 = ([],[u1,u2])


------------------------- Assignment 3

sub_u :: Sub -> [Upair] -> [Upair]
sub_u  _ [] = []
sub_u s ((t1, t2) : xs) = ((sub s t1), (sub s t2)) : sub_u s xs


step :: State -> State
step (ss, []) = (ss, [])
step (ss, (t1, t2) : us) 
  -- case a: α ↔ α : return (S, U)
  | t1 == t2 = (ss, us)
  -- case b or c
  | otherwise  = bAndC(ss, (t1, t2) : us) 
  where 
    bAndC :: State -> State
    -- case b: α ↔ τ
    bAndC (ss, (At alpha, tau) : us) = if alpha `occurs` tau then error ("Step: atom " ++ alpha ++ " occurs in " ++ show tau) else ((alpha, tau) : ss, sub_u (alpha, tau) us)
    -- case b: τ ↔ α
    bAndC (ss, (tau, At alpha) : us) = if alpha `occurs` tau then error ("Step: atom " ++ alpha ++ " occurs in " ++ show tau) else ((alpha, tau) : ss, sub_u (alpha, tau) us)
    -- case c: (σ 1 → σ 2 ) ↔ (τ 1 → τ 2 ) : return (S, {σ 1 ↔ τ 1 , σ 2 ↔ τ 2 } ∪ U )
    bAndC (ss, (sigma1 :-> sigma2, tau1 :-> tau2) : us) = (ss, (sigma1, tau1) : (sigma2, tau2) : us)


unify :: [Upair] -> [Sub]
unify us = unificationAlgorithm ([], us)
  where
    unificationAlgorithm :: State -> [Sub]
    unificationAlgorithm (ss, []) = ss
    unificationAlgorithm (ss, us) = unificationAlgorithm (step (ss, us))



------------------------- Assignment 4

type Context   = [(Var,Type)]
type Judgement = (Context, Term, Type)

data Derivation = 
    Axiom Judgement
    | Abstraction Judgement Derivation
    | Application Judgement Derivation Derivation



n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")

n2 = Lambda "x" (Apply(Variable "x") (Variable "y"))  


d1 = Application ([("y",At "a")], n1 , At "a") (
       Abstraction ([("y",At "a")],Lambda "x" (Variable "x"),At "a" :-> At "a") (
         Axiom ([("x",At "a"),("y",At "a")],Variable "x",At "a")
     ) ) (
       Axiom ([("y",At "a")], Variable "y", At "a")
     )

d2 = Application ([("y",At "b")],Apply (Lambda "x" (Apply (Variable "x") (Variable "y"))) (Lambda "z" (Variable "z")),At "a") (
       Abstraction ([("y",At "b")],Lambda "x" (Apply (Variable "x") (Variable "y")),At "c") (
         Application ([("x",At "d"),("y",At "b")],Apply (Variable "x") (Variable "y"),At "e") (
           Axiom ([("x",At "d"),("y",At "b")],Variable "x",At "f")
         ) (
           Axiom ([("x",At "d"),("y",At "b")],Variable "y",At "g")
     ) ) ) (
       Abstraction ([("y",At "b")],Lambda "z" (Variable "z"),At "h") (
         Axiom ([("z",At "i"),("y",At "b")],Variable "z",At "j")
     ) )



conclusion :: Derivation -> Judgement
conclusion (Axiom j) = j
conclusion (Abstraction j _) = j
conclusion (Application j _ _) = j

subs_ctx :: [Sub] -> Context -> Context
subs_ctx _ [] = []
subs_ctx ss ((v, t) : cs) =  (v, (subs ss t)) : subs_ctx ss cs

subs_jdg :: [Sub] -> Judgement -> Judgement
subs_jdg ss (c, term, _type) = (subs_ctx ss c, term, subs ss _type)

subs_der :: [Sub] -> Derivation -> Derivation
subs_der ss (Axiom j) = Axiom (subs_jdg ss j)
subs_der ss (Abstraction j d) = Abstraction (subs_jdg ss j) (subs_der ss d)
subs_der ss (Application j d1 d2) = Application (subs_jdg ss j) (subs_der ss d1) ( subs_der ss d2)


------------------------- Typesetting derivations


instance Show Derivation where
  show d = unlines (reverse strs)
    where
      (_,_,_,strs) = showD d

      showC :: Context -> String
      showC [] = []
      showC [(x,t)]    = x ++ ": " ++ show t
      showC ((x,t):cx) = x ++ ": " ++ show t  ++ " , " ++ showC cx

      showJ :: Judgement -> String
      showJ ([],n,t) =              "|- " ++ show n ++ " : " ++ show t
      showJ (cx,n,t) = showC cx ++ " |- " ++ show n ++ " : " ++ show t

      showL :: Int -> Int -> Int -> String
      showL l m r = replicate l ' ' ++ replicate m '-' ++ replicate r ' '

      showD :: Derivation -> (Int,Int,Int,[String])
      showD (Axiom j) = (0,k,0,[s,showL 0 k 0]) where s = showJ j; k = length s
      showD (Abstraction j d)   = addrule (showJ j) (showD d)
      showD (Application j d e) = addrule (showJ j) (sidebyside (showD d) (showD e))

      addrule :: String -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      addrule x (l,m,r,xs)
        | k <= m     = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL  l m r  : xs)
        | k <= l+m+r = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL ll k rr : xs)
        | otherwise  = (0,k,0, x : replicate k '-' : [ replicate (-ll) ' ' ++ y ++ replicate (-rr) ' ' | y <- xs])
        where
          k = length x
          i = div (m - k) 2
          ll = l+i
          rr = r+m-k-i

      extend :: Int -> [String] -> [String]
      extend i strs = strs ++ repeat (replicate i ' ')

      sidebyside :: (Int,Int,Int,[String]) -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      sidebyside (l1,m1,r1,d1) (l2,m2,r2,d2)
        | length d1 > length d2 = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip d1 (extend (l2+m2+r2) d2)])
        | otherwise             = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip (extend (l1+m1+r1) d1) d2])


------------------------- Assignment 5

mergeContext :: Context -> Context -> Context
mergeContext xs [] = xs
mergeContext [] ys = ys
mergeContext ((x1, x2):xs) ((y1, y2):ys)
    | x1 == y1   = (x1, x2) : mergeContext xs ys
    | x1 <= y1   = (x1,x2) : mergeContext xs ((y1, y2):ys)
    | otherwise = (y1, y2) : mergeContext ((x1, x2):xs) ys

mapFree :: [Var] -> [(Var, Type)]
mapFree [] = []
mapFree (x : xs) = (x, At "") : mapFree xs

mapAtoms :: [Var] -> [Atom] -> [(Var, Type)]
mapAtoms [] _ = []
mapAtoms (var: vars) (atom : atoms) = (var, At atom) : mapAtoms vars atoms

derive0 :: Term -> Derivation
derive0 term = aux (mapFree (free term), term, At "")
  where
    aux :: Judgement -> Derivation
    aux (c, Variable x, t) =  Axiom (c `mergeContext` [(x, At "")], Variable x, t)
    aux (c, Lambda x n, t) = Abstraction (c `mergeContext` mapFree (free (Lambda x n)), Lambda x n, t) (aux (c `mergeContext` mapFree (free (Lambda x n)), n, t))
    aux (c, Apply n m, t) = Application (c `mergeContext` mapFree (free (Apply n m)), Apply n m, t) (aux (c `mergeContext` mapFree (free (Apply n m)), n, t)) (aux (c `mergeContext` mapFree (free (Apply n m)), m, t))


derive1 :: Term -> Derivation
derive1 term = aux (tail (tail atoms)) (mapAtoms (free term) (tail atoms), term, At (head atoms))
  where
    aux :: [Atom] -> Judgement -> Derivation
    aux atomList (c, Variable x, t) =  Axiom (c `mergeContext` [(x, At (head (tail(tail atomList))))], Variable x, t)
    aux atomList (c, Lambda x n, t) = Abstraction (c `mergeContext` mapAtoms (free (Lambda x n)) (tail (tail atomList)), Lambda x n, t) (aux (tail atomList) (c `mergeContext` mapAtoms (free (Lambda x n)) atomList, n, At (head (tail atomList))))
    aux atomList (c, Apply n m, t) = Application (c `mergeContext` mapAtoms (free (Apply n m)) (tail (tail atomList)), Apply n m, t) (aux (tail atomList) (c `mergeContext` mapAtoms (free (Apply n m)) atomList, n, At (head atomList))) (aux (tail (tail atomList)) (c `mergeContext` mapAtoms (free (Apply n m)) atomList, m, At (head (tail atomList))))


findTypeOfVar :: Context -> Var -> Type
findTypeOfVar [] _ = At ""
findTypeOfVar ((v, t):xs) varToFind = if v == varToFind then t else findTypeOfVar xs varToFind

getTypeOfVarFromDerivation :: Derivation -> Var -> Type
getTypeOfVarFromDerivation d = findTypeOfVar (get1st(conclusion d))
  where
    get1st (x, _, _) = x

getTypeFromDerivation :: Derivation -> Type
getTypeFromDerivation d = get3rd (conclusion d)
  where
    get3rd (_,_,x) = x


upairs :: Derivation -> [Upair]
upairs d = aux d []
  where
    aux :: Derivation -> [Upair] -> [Upair]
    -- variable
    aux (Axiom (c, Variable v, t)) upairList = upairList ++ [(t, findTypeOfVar c v)]
    -- abstraction
    aux (Abstraction (c, Lambda x n, t) der) upairList = upairList ++ [(t, getTypeOfVarFromDerivation der x :-> getTypeFromDerivation der)] ++ aux der []
    -- application
    aux (Application (c, Apply n m, t) der1 der2) upairList = upairList ++ [(getTypeFromDerivation der1, getTypeFromDerivation der2 :-> t)] ++ aux der1 [] ++ aux der2 []


derive :: Term -> Derivation
derive t = aux (derive1 t)
  where
    aux :: Derivation -> Derivation
    aux der = subs_der (unify (upairs der)) der

