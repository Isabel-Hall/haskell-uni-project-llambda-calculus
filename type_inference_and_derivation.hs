
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

--Determine if an atom occurs in a type
occurs :: Atom -> Type -> Bool
occurs a (At b)       = a == b
occurs a (At b :-> s) = a == b || occurs a s
occurs a (t :-> s)    = occurs a t || occurs a s

--Return the atoms that occur in a type in an alphabetical list
findAtoms :: Type -> [Atom]
findAtoms (At a)       = [a]
findAtoms (At a :-> s) = [a] `merge` findAtoms s
findAtoms (t :-> s)    = findAtoms t `merge` findAtoms s


------------------------- Type substitution

type Sub = (Atom,Type)

s1 :: Sub
s1 = ("a", At "e")

s2 :: Sub
s2 = ("e", At "b" :-> At "c")

s3 :: Sub
s3 = ("c", At "a" :-> At "a")


------------------------- Assignment 2

--Apply a substitution, following the rules of the lambda calculus
sub :: Sub -> Type -> Type
sub (a, t) (At b)
  | a == b               = t
  | otherwise            = At b
sub (a, t) (At b :-> s)
  | a == b && occurs a s = t :-> sub (a, t) s
  | a == b               = t :-> s
  |           occurs a s = At b :-> sub (a, t) s
  | otherwise            = At b :-> s
sub (a, t) (b :-> s)     = sub (a, t) b :-> sub (a, t) s

--Apply a list of substitutions to a type, applying the head of the list last
subs :: [Sub] -> Type -> Type
subs xs t = foldr sub t xs


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

--Apply a substitution to a list of unification pairs
sub_u :: Sub -> [Upair] -> [Upair]
sub_u s us = [((sub s u1), (sub s u2)) | (u1, u2) <- us]


--Carry out a single transition of the unification algorithm from the lambda calculus
step :: State -> State
step (ss, [])    = (ss, [])
step (ss, (At u1, At u2): us)
  | u1 == u2     = (ss, us)
step (ss, (At u1, u2): us) 
  | occurs u1 u2 = error ("Step: atom " ++ show u1 ++ " occurs in " ++ show u2)
  | otherwise    = (ss ++ [newSub], sub_u newSub us)
    where
      newSub :: Sub
      newSub = (u1, u2)
step (ss, (u1, At u2): us)
  | occurs u2 u1 = error ("Step: atom " ++ show u2 ++ " occurs in " ++ show u1)
  | otherwise    = (ss ++ [newSub], sub_u newSub us)
    where
      newSub :: Sub
      newSub = (u2, u1)
step (ss, (u1, u2): us) = (ss, [(u1', u2'),(u1'', u2'')] ++ us)
  where
    (u1':-> u1'') = u1
    (u2':-> u2'') = u2


--Carry out the full unification algorithm
unify :: [Upair] -> [Sub]
unify [] = []
unify us = unify us' ++ ss
  where (ss, us') = step ([], us)


------------------------- Assignment 4

--Create types for Context, Judgement and Derivation
type Context   = [(Var, Type)]
type Judgement = (Context, Term, Type)

data Derivation = 
    Axiom       Judgement 
  | Abstraction Judgement Derivation
  | Application Judgement Derivation Derivation

n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")


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


--Extract the concluding judgement from a derivation
conclusion :: Derivation -> Judgement
conclusion (Axiom j)           = j
conclusion (Abstraction j _)   = j 
conclusion (Application j _ _) = j

--Apply a list of substitutions to every type in a Context
subs_ctx :: [Sub] -> Context -> Context
subs_ctx ss ctx = [(v, (subs ss t)) | (v, t) <- ctx]

--Apply a list of substitutions to every type in a Judgement
subs_jdg :: [Sub] -> Judgement -> Judgement
subs_jdg ss (ctx, ter, typ) = ((subs_ctx ss ctx), ter, (subs ss typ))

--Apply a list of substitutions to every type in a Derivation
subs_der :: [Sub] -> Derivation -> Derivation
subs_der ss (Axiom j)             = Axiom (subs_jdg ss j)
subs_der ss (Abstraction j d)     = Abstraction (subs_jdg ss j) (subs_der ss d)
subs_der ss (Application j d1 d2) = Application (subs_jdg ss j) (subs_der ss d1) (subs_der ss d2)


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

--Create an incomplete derivation from a lambda term (leaving the types empty as At "")
derive0 :: Term -> Derivation
derive0 t = aux ([(var, At "") | var <- free t], t, At "")
  where
    aux :: Judgement -> Derivation
    aux (ctx, Variable x, typ) = Axiom (ctx, Variable x, typ)
    aux (ctx, Lambda x t, typ) = Abstraction (ctx, Lambda x t, typ) (aux (addContext ctx x, t, At ""))
      where
        addContext ctx x = [(v, t) | (v, t) <- ctx, v /= x] ++ [(x, At "")]
    aux (ctx, Apply m n, typ)  = Application (ctx, Apply m n, typ) (aux (ctx, m, At "")) (aux (ctx, n, At ""))

--Create an incomplete derivation from a lambda term, where all the types are fresh atoms
derive1 :: Term -> Derivation
derive1 t = aux (drop (1 + length (free t)) atoms) ([(var, At om) | (var, om) <- zip (free t) (tail atoms)], t, At (head atoms))
  where
    aux :: [Atom] -> Judgement -> Derivation
    aux ats (ctx, Variable x, typ) = Axiom (ctx, Variable x, typ)
    aux ats (ctx, Lambda x t, typ) = Abstraction (ctx, Lambda x t, typ) (aux (drop 2 ats) (addContext ctx x, t, At (ats !! 1)))
      where addContext ctx x = (x, At (head ats)) : [(v, t) | (v, t) <- ctx, v /= x]
    aux ats (ctx, Apply m n, typ)  = Application (ctx, Apply m n, typ) (aux evenAts (ctx, m, At (ats !! 0))) (aux oddAts (ctx, n, At (ats !! 1)))
      where
        evenAts = tail [a | (a, i) <- zip ats [1..], even i]
        oddAts  = tail [a | (a, i) <- zip ats [1..], odd i]

--Extract unification pairs from an incomplete derivation, generated using derive1
upairs :: Derivation -> [Upair]
upairs (Axiom (ctx, Variable t, typ))         = [(typ, getTypeCtx ctx t)]
upairs (Abstraction (ctx, Lambda x t, typ) d) = (typ, getTypeCtx (getContextDer d) x :-> getTypeDer d) : upairs d
upairs (Application (ctx, _, typ) d1 d2)      = [(getTypeDer d1, getTypeDer d2 :-> typ)] ++ upairs d1 ++ upairs d2


getTypeCtx :: Context -> Var -> Type
getTypeCtx ctx v = snd (head [c | c <- ctx, fst c == v])

getTypeDer :: Derivation -> Type
getTypeDer (Axiom (_, _, typ))           = typ
getTypeDer (Abstraction (_, _, typ) _)   = typ
getTypeDer (Application (_, _, typ) _ _) = typ

getContextDer :: Derivation -> Context
getContextDer (Axiom (ctx, _, _))             = ctx 
getContextDer (Abstraction (ctx, _, _) d)     = ctx 
getContextDer (Application (ctx, _, _) d1 d2) = ctx 

--Produce a type derivation for a term, if one exists
derive :: Term -> Derivation
derive t = subs_der (unify (upairs der)) der
  where der = derive1 t

------------------------ Tests
n = Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "x")(Variable "z"))(Apply (Variable "y")(Variable "z")))))

n' = Lambda "x" (Apply (Lambda "x" (Lambda "x" (Variable "x"))) (Lambda "x" (Lambda "x" (Variable "x"))))

t'1 = Lambda "x" (Lambda "y" (Lambda "z" (Apply (Variable "z") (Variable "x"))))

t'2 = Lambda "f" (Lambda "g" (Apply (Variable "f")(Lambda "x"(Apply(Apply (Variable "g")(Variable "x"))(Variable "x")))))

suc = Lambda "n" (Lambda "f" (Lambda "x" (Apply (Variable "f")(Apply (Apply (Variable "n")(Variable "f"))(Variable "x")))))

ad = Lambda "m" (Lambda "n" (Lambda "f" (Lambda "x" (Apply (Apply (Variable "m") (Variable "f")) (Apply (Apply (Variable "n") (Variable "f"))(Variable "x"))))))

ter = Lambda "y" (Apply (Apply (Apply (Lambda "x" (Variable "x")) (Variable "y")) (Lambda "x" (Variable "x"))) (Variable "x"))

terb = Lambda "y" (Apply (Lambda "x" (Apply (Variable "x") (Lambda "y" (Apply (Variable "x") (Variable "y"))))) (Lambda "x" (Apply (Variable "x") (Variable "y"))))

m = Lambda "f" (Lambda "g" (Lambda "x" (Apply (Variable "g") (Apply (Apply (Variable "f") (Variable "x")) (Variable "x")))))

ter3i = Lambda "x" (Lambda "y" (Variable "x"))

ter3ia = Lambda "x" (Lambda "y" (Lambda "z" (Variable "y")))
ter3ib = Lambda "w" (Variable "w")

ter3 = Apply (Apply m ter3ia) ter3ib

ter4 = Apply (Lambda "x" (Variable "y")) (Variable "x")