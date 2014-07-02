{-# LANGUAGE TypeFamilies, GADTs, FlexibleContexts, FlexibleInstances
              , UndecidableInstances, TypeOperators #-}
module SimpleExp where

import Control.Monad
import Control.Monad.State
import Control.Applicative
import Text.Printf

infixl :^

data E a where
  Op   :: Op a -> E a
  Var  :: V a -> E a
  (:^) :: HasType a => E (a -> b) -> E a -> E b
  Lam  :: HasType a => V a -> E b -> E (a -> b)


data Op :: * -> * where
  Lit       :: Float -> Op Float
  AddFloat  :: Op (Float -> Float -> Float)
  Pair      :: Op (a -> b -> (a,b))
  Fst       :: Op ((a,b) -> a)
  Snd       :: Op ((a,b) -> b)

data Type :: * -> * where
  FloatT :: Type Float
  (:*:)  :: (HasType a, HasType b) => Type a -> Type b -> Type (a, b)
  (:->:) :: (HasType a, HasType b) => Type a -> Type b -> Type (a -> b)


-- | Variable name
type Id = String

-- | Typed variables
data V a = V { varName :: Id, varType :: Type a }


{------------------------------------------
      class HasType
-------------------------------------------}
class HasType t where typeT :: Type t


instance (HasType a, HasType b) =>
  HasType (a, b) where typeT = typeT :*: typeT

instance (HasType a, HasType b) =>
  HasType (a->b) where typeT = typeT :->: typeT

instance HasType Float where typeT = FloatT


{-----------------------------------
    Convenience functions
------------------------------------}

pairE :: (HasType a, HasType b) => E a -> E b -> E (a,b)
pairE = op2 Pair

fstE :: (HasType a, HasType b) => E (a,b) -> E a
fstE = op1 Fst

sndE :: (HasType a, HasType b) => E (a,b) -> E b
sndE = op1 Snd

instance Num (E Float) where
  fromInteger x = Op (Lit (fromIntegral x))
  a + b         = (Op AddFloat) :^ a :^ b
  (-)           = error "not defined"
  (*)           = error "not defined"
  abs           = error "not defined"
  signum        = error "not defined"

{------------------------------
   ToE, FromE classes. For notational convenience.

   e.g. want to work on "pair of expressions" not an "expression of a pair".
-------------------------------}
class ToE a where
  type ExpT a
  toEN :: a -> NameM (E (ExpT a))

-- | Convert to an expression, using fresh name supply
toE :: ToE w => w -> E (ExpT w)
toE = runNameM . toEN

class ToE a => FromE a where
  fromE :: E (ExpT a) -> a

instance ( FromE u, HasType (ExpT u)
         , FromE v, HasType (ExpT v)
         ) => FromE (u,v) where
  fromE e = (fromE eu, fromE ev) where (eu,ev) = (fstE e, sndE e)

{---------------------------------
   ToE, FromE instances
----------------------------------}

instance ToE (E a) where
  type ExpT (E a) = a
  toEN = return

instance FromE (E a) where
  fromE = id

instance (ToE u, HasType (ExpT u),
          ToE v, HasType (ExpT v))
         => ToE (u,v) where
  type ExpT (u,v) = (ExpT u, ExpT v)
  toEN (u,v) =  liftM2 (op2 Pair)  (toEN u) (toEN v)


{-instance (FromE u, ToE v, HasType (ExpT u)) => ToE (u -> v) where
  type ExpT (u -> v) = ExpT u -> ExpT v
  toEN f = do u <- genVar
              b <- toEN (f (fromE (Var u)))
              return $ Lam u b -}

{--------------------------------------------------------------------
    Convenient n-ary operator application
--------------------------------------------------------------------}

-- | Convenient operator application
op1 :: (HasType a, HasType b) =>
       Op (a -> b) -> E a -> E b
op1 o a = Op o :^ a

-- | Convenient operator application
op2 :: (HasType a, HasType b, HasType c) =>
       Op (a -> b -> c) -> E a -> E b -> E c
op2 o a b = op1 o a :^ b

{------------------------
     variable generation
-------------------------}

genVar :: HasType a => NameM (V a)
genVar = var <$> genName

var :: HasType a => Id -> V a
var = flip V typeT

{-------------------------------------
  Show instances
--------------------------------------}

instance Show (Op t) where
  show op = case op of
    Lit f        -> printf "(Lit %f)" f
    AddFloat     -> "AddFloat"
    Pair         -> "Pair"
    Fst          -> "Fst"
    Snd          -> "Snd"

instance Show (E t) where
  show e = case e of
    Op op    -> show op
    Var v    -> "Var " ++ show v
    (:^) f a -> show f ++ " :^ " ++ show a
    Lam v b  -> "Lam " ++ show v ++ show b

instance Show (V t) where
  show v = printf "(V %s :: %s)" (show (varName v)) (show (varType v))

instance Show (Type t) where
  show t = case t of
    FloatT      -> "Float"
    (:*:) t t'  -> printf "(%s,%s)" (show t) (show t')
    (:->:) t t' -> printf "(%s -> %s)" (show t) (show t')

{------------------------
    Name monad
-------------------------}

type NameM = State [String]

-- Generate a new variable name
genName :: State [x] x
genName = do x:xs' <- get
             put xs'
             return x

runNameM :: NameM a -> a
runNameM m = evalState m allNames

allNames :: [String]
allNames = map reverse (tail names)
 where
   names = "" : [ c:cs | cs <- names , c <- ['a' .. 'z'] ]

-----------------------------------------


{----------------------------
     Complex
-----------------------------}

--
-- Complex is NOT part of the types for the language
-- But by writing ToE and FromE instances we can use it
-- in day to day usage.
--

data Complex a = Complex a a

instance (ToE a, HasType (ExpT a)) => ToE (Complex a) where
  type ExpT (Complex a) = (ExpT a, ExpT a)
  toEN (Complex a b) = toEN (a, b)

instance FromE (Complex (E Float)) where
  fromE p = Complex a b
    where (a,b) = (fstE p, sndE p)


{-----------------------------
    Compilation
-------------------------------}

-- | Construct an 'E' transformer from an 'ExpT' transformer
compile1 :: (FromE v, FromE w) => (v -> w) -> (E (ExpT v) -> E (ExpT w))
compile1 f = toE . f . fromE



{---------------------------------
     Demonstration
----------------------------------}


test :: (E Float, E Float) -> E Float
test (x,y) = x + y

higherLevel :: Complex (E Float)-> E Float
higherLevel (Complex a b) = a + b

test2 :: E Float -> (E Float, E Float)
test2 x = (x+1,x+2)

vx :: HasType a => E a
vx = Var (var "x")


--------------------------------

{-
   1. Show E data type
   2. Show Op
   3. The Type and HasType class might not seem like they're that useful.
      It is used to reflect the type so that we can write functions that operate on the type
      This is useful in code generation. e.g. Flattening out a tuple into two variable bindings in
      GLSL.


-}

{-

  1. Apply "test" to "variable". Show it doesn't work.
  2. compile "test" and show that type is slightly different. Apply to test variable and show
     generated code.

     Point out that you can see the types in the output.

  3. Talk about ToE and FromE instances and how this provides even more convenience. Show
     "higherLevel"
  4. Show "test2" as well.


-}
