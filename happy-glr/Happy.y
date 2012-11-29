{
import Control.Applicative(Applicative(..))
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..), foldMapDefault, fmapDefault)
}

%tokentype { Char }
%lexer { id } { [] }

%token
  '1' { '1' }

%%

E :: {AST ForestId}
  : E E E     { Triple $1 $2 $3 }
  | '1'       { One }
  |           { Empty }

{
-- We need this workaround to define Show (Fix f) in HappyMain
-- without any UndecidableInstances
class Show1 f where
    show1 :: Show a => f a -> String

instance (Show1 f, Show a) => Show (f a) where
    show = show1


-- Keep the parse tree type polymorphic in subtree type for flexibility
data AST ast = Triple ast ast ast | One | Empty
             deriving (Show)

--deriving instance Show ast => Show (AST ast)

instance Functor AST where
    fmap = fmapDefault

instance Foldable AST where
    foldMap = foldMapDefault

instance Traversable AST where
    traverse f (Triple a b c) = pure Triple <*> f a <*> f b <*> f c
    traverse _ One = pure One
    traverse _ Empty = pure Empty


instance Show1 AST where
    show1 = show
}
