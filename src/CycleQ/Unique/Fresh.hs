module CycleQ.Unique.Fresh
  ( -- * Fresh Monad
    FreshM,
    runFreshM,

    -- * Fresh Monad Class
    MonadFresh (..),
    freshen,
    freshVar,
    freshenClause,
  )
where

import Control.Monad.Reader
import Control.Monad.ST
import CycleQ.Syntax
import CycleQ.Unique.Unique
import Data.Map qualified as Map
import Data.STRef

-- * Fresh Monad

-- | The base unique supplier.
newtype FreshM s a = FreshM
  { unFreshM :: STRef s Int -> ST s a
  }
  deriving
    (Functor, Applicative, Monad)
    via ReaderT (STRef s Int) (ST s)

-- | Run a @Unique@ action.
runFreshM :: (forall s. FreshM s a) -> a
runFreshM go = runST $ do
  countPtr <- newSTRef 0
  unFreshM go countPtr

-- * Monad Class

-- | A monad with the ability to a fresh produce @Unique@.
class (Monad m) => MonadFresh m where
  -- | A fresh @Unique@.
  freshUnique :: m Unique

instance MonadFresh (FreshM s) where
  freshUnique =
    FreshM $ \countPtr -> do
      next <- readSTRef countPtr
      writeSTRef countPtr (next + 1)
      pure (CycleQ next)

instance
  (MonadTrans t, Monad (t m), MonadFresh m) =>
  MonadFresh (t m)
  where
  freshUnique = lift freshUnique

-- | Assign a new unique to the given object.
freshen :: (HasUnique a, MonadFresh m) => a -> m a
freshen x = setUnique x <$> freshUnique

-- | Create a fresh unnamed variable of the given type.
freshVar :: (MonadFresh m) => Type -> m Var
freshVar ty = do
  unique <- freshUnique
  pure
    MkVar
      { varName = "_" ++ show unique,
        varType = Forall [] ty,
        varUnique = unique
      }

-- | Create a fresh instance of a clause.
-- N.B. Hypothesis rules return to equations.
freshenClause :: (MonadFresh m) => Clause -> m (TySubst, Subst, Clause)
freshenClause clause = do
  -- Freshen universally quantified variables
  freshVars <- forM (clauseVars clause) $ \x -> do
    x' <- freshen x
    pure (x, x')

  -- Freshen universally quantified type variables
  freshTyVars <- forM (clauseTyVars clause) $ \a -> do
    a' <- freshen a
    pure (a, a')

  -- Create substitutions
  let theta = Map.fromList [(x, Var x' []) | (x, x') <- freshVars]
      tyTheta = Map.fromList [(a, TyVar a' []) | (a, a') <- freshTyVars]

  -- Apply substitutions to the hypotheses and goal.
  let clause' =
        Clause
          { clauseVars = fmap snd freshVars,
            clauseTyVars = fmap snd freshTyVars,
            clauseHypEqs =
              fmap
                (substEquation tyTheta theta)
                ( clauseHypEqs clause
                    ++ clauseHypRules clause
                ),
            clauseHypRules = [],
            clauseGoal =
              fmap (substEquation tyTheta theta) (clauseGoal clause)
          }
  pure (tyTheta, theta, clause')
