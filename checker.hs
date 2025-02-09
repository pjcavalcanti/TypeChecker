import Test.HUnit
import Data.List (find)
import qualified Data.Set as Set

data Type = TypeVar String | TypeArrow Type Type
  deriving (Eq, Ord, Show)
data Term = TermVar String | TermApp Term Term | TermLambda Term Type Term
  deriving (Eq, Ord, Show)

type Context = Set.Set (Term, Type)

isContextValid :: Context -> Bool
isContextValid context = fst (foldr f (True, Set.empty) context)
  where
    f (TermApp _ _, _) (_, _) = (False, Set.empty)
    f (TermLambda _ _ _, _) (_, _) = (False, Set.empty)
    f (TermVar x, _) (True, seen) =
      if x `Set.member` seen
        then (False, seen)
        else (True, (Set.insert x seen))
    f _ (_, seen) = (False, seen)

getType :: Context -> Term -> Maybe Type
getType context (TermVar x)
  | not $ isContextValid context = Nothing  -- these checks could be done less often
  | otherwise = fmap snd $ find isX (Set.toList context)
  where
    isX (TermVar y, _) = x == y
    isX _ = False
getType context (TermApp x y)
  | not $ isContextValid context = Nothing
  | otherwise = 
    let sigma = getType context y
        sigma_tau = getType context x
    in case (sigma, sigma_tau) of
      (Just t_sigma, Just (TypeArrow t_sigma_p t_tau)) ->
        if t_sigma == t_sigma_p
          then Just t_tau
          else Nothing
      _ -> Nothing
getType context (TermLambda x sigma y)
  | not $ isContextValid context = Nothing 
  | otherwise =
    case x of
      TermVar xp ->
        let tau = getType (Set.insert (TermVar xp, sigma) context) y
        in case tau of
          Nothing -> Nothing
          Just t -> Just (TypeArrow sigma t)
      _ -> Nothing

isValidJudgement :: Context -> Term -> Type -> Bool
isValidJudgement context (TermVar x) tau = (getType context (TermVar x)) == Just tau
isValidJudgement context (TermApp m n) tau = (getType context (TermApp m n)) == Just tau
isValidJudgement context (TermLambda x s m) tau = (getType context (TermLambda x s m)) == Just tau


-- A few tests:

-- Test data (suggested by gpt 4o!)
  
-- Bool
-- Int
-- x
-- y
tBool = TypeVar "Bool"
tInt  = TypeVar "Int"
x = TermVar "x"
y = TermVar "y"

-- λx: Bool → x
-- λx: Int → x
-- λx: Bool. λy: Int → x
-- (idBool x)
idBool = TermLambda (TermVar "x") tBool (TermVar "x")
idInt  = TermLambda (TermVar "x") tInt (TermVar "x")
constBI = TermLambda (TermVar "x") tBool (TermLambda (TermVar "y") tInt (TermVar "x"))
appIdBool = TermApp idBool x

-- {x: Bool}
-- {x: Bool, y: Int}
-- {}
-- {λz: Int → z : Int}
ctx1 = Set.fromList [(x, tBool)] 
ctx2 = Set.fromList [(TermVar "x", tBool), (TermVar "y", tInt)]
emptyCtx = Set.fromList []
invalidCtx = Set.fromList [(TermLambda (TermVar "z") tInt (TermVar "z"), tInt)]  

-- Test cases

testGetType :: Test
testGetType = TestList
  [ "testGet1" ~: getType ctx1 x ~?= Just tBool
  , "testGet2" ~: getType ctx2 y ~?= Just tInt
  , "testGet3" ~: getType ctx1 y ~?= Nothing
  , "testGet4" ~: getType emptyCtx idBool ~?= Just (TypeArrow tBool tBool)
  , "testGet5" ~: getType emptyCtx constBI ~?= Just (TypeArrow tBool (TypeArrow tInt tBool))
  , "testGetInvalid" ~: getType invalidCtx x ~?= Nothing
  , "testApp1" ~: getType ctx1 appIdBool ~?= Just tBool
  , "testAppWrong" ~: getType ctx1 (TermApp idBool y) ~?= Nothing
  ]

testIsValidJudgement :: Test
testIsValidJudgement = TestList
  [ "testJudg1" ~: isValidJudgement ctx1 x tBool ~?= True
  , "testJudg2" ~: isValidJudgement ctx2 y tInt ~?= True
  , "testJudg3" ~: isValidJudgement emptyCtx idBool (TypeArrow tBool tBool) ~?= True
  , "testJudg4" ~: isValidJudgement emptyCtx constBI (TypeArrow tBool (TypeArrow tInt tBool)) ~?= True
  , "testJudgWrong" ~: isValidJudgement ctx1 idBool (TypeArrow tInt tBool) ~?= False
  , "testJudgInvalid" ~: isValidJudgement invalidCtx x tInt ~?= False
  ]

tests :: IO ()
tests= do
  putStrLn "Running getType tests..."
  _ <- runTestTT testGetType
  putStrLn "\nRunning isValidJudgement tests..."
  _ <- runTestTT testIsValidJudgement
  return ()
