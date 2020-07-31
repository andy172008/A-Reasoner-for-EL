--author:SX1916085 贺星宇
module Main where

import Lib

--定义"概念"Concept
data Concept = Top | Concept String | Concept `Conjunction` Concept | Role `Exist` Concept deriving (Eq, Show)

--定义"属性"Role
newtype Role = Role String deriving (Eq, Show)

--定义"公理"Axiom
data Axiom = Concept `Implies` Concept | Concept `Equivalence` Concept deriving (Eq, Show)

--定义TBox
type TBox = [Axiom]

--这里采用了Haskell中Record Syntax这个特性，这个特性的好处在于可以用函数从中直接按项取值
data Super = Super {self :: Concept, sup :: [Concept]} deriving (Eq, Show)

--将一条axiom化简，返回若干条axiom也就是TBox
normalisationOneAxiom :: Int -> Axiom -> TBox
normalisationOneAxiom i axiom = case axiom of
  a `Equivalence` b -> [a `Implies` b, b `Implies` a]
  a `Implies` (b `Conjunction` c) -> [a `Implies` b, a `Implies` c]
  a `Implies` b ->
    if isComplex a && isComplex b
      then [a `Implies` Concept ("new" ++ show i), Concept ("new" ++ show i) `Implies` b]
      else
        if isComplex a
          then [fst (divideByTuple i a) `Implies` Concept ("new" ++ show i), snd (divideByTuple i a) `Implies` b]
          else
            if isComplex b
              then [a `Implies` snd (divideByTuple i b), Concept ("new" ++ show i) `Implies` fst (divideByTuple i b)] --NF5
              else [axiom]

--先将TBox中的第一条化简，再不断迭代，直到TBox中的所有axiom化简完成
normalisation :: Int -> TBox -> TBox
normalisation _ [] = []
normalisation i (axiom : others) =
  if head oneOutput == axiom
    then axiom : normalisation (i + 1) (tail oneOutput ++ others)
    else normalisation (i + 1) (oneOutput ++ others)
  where
    oneOutput = normalisationOneAxiom i axiom

--判断一个concept是否是复杂概念
isComplex :: Concept -> Bool
isComplex concept = case concept of
  a `Conjunction` b -> isComplex' a || isComplex' b
  _ `Exist` a -> isComplex' a
  _ -> False

isComplex' :: Concept -> Bool
isComplex' concept = case concept of
  Conjunction _ _ -> True
  Exist _ _ -> True
  _ -> False

--将一个concept进行切割，便于其他函数调用
divideByTuple :: Int -> Concept -> (Concept, Concept)
divideByTuple i concept = case concept of
  a `Exist` b -> (b, a `Exist` Concept ("new" ++ show i))
  a `Conjunction` b ->
    if isComplex' a
      then (a, Conjunction (Concept ("new" ++ show i)) b)
      else (b, Conjunction (Concept ("new" ++ show i)) a)

cons :: TBox -> [Super]
cons ts = init (unique (extract ts))
  where
    init [] = []
    init (c : cs) = Super c [c, Top] : init cs

extract :: TBox -> [Concept]
extract [] = []
extract (t : ts) = extract' t ++ extract ts

extract' :: Axiom -> [Concept]
extract' (a `Implies` b) = extr a ++ extr b
  where
    extr c = case c of
      Conjunction e f -> extr e ++ extr f
      Exist _ d -> extr d
      Top -> []
      _ -> [c]

unique :: Eq a => [a] -> [a]
unique (x : y : lst) =
  if x `elem` y : lst
    then unique (y : lst)
    else x : unique (y : lst)
unique lst = lst

run :: TBox -> Concept -> Concept -> Bool
run ts a b = check norms norms supers a b
  where
    norms = normalisation 1 ts
    supers = cons norms

check :: TBox -> TBox -> [Super] -> Concept -> Concept -> Bool
check _ [] ssc a b = suc a b ssc
check tsc (t : ts) ssc a b = case t of
  Conjunction a1 a2 `Implies` a3 ->
    suc a b ssc
      || (if r1 /= ssc then check tsc tsc r1 a b else check tsc ts ssc a b)
    where
      r1 = rule1 a1 a2 a3 ssc
      rule1 _ _ _ [] = []
      rule1 a1 a2 a3 (s : ss) =
        if (a1 `elem` (sup s) && a2 `elem` (sup s))
          then s {sup = unique (a3 : (sup s))} : (rule1 a1 a2 a3 ss)
          else s : (rule1 a1 a2 a3 ss)
  b1 `Implies` Exist b2 b3 ->
    if suc a b ssc
      then True --R2
      else
        if r2 /= tsc
          then check r2 r2 ssc a b
          else check tsc ts ssc a b
    where
      r2 = unique (rule2 b1 b2 b3 tsc ssc)
      rule2 _ _ _ tt [] = tt
      rule2 b1 b2 b3 tt (s : ss) =
        if (b1 `elem` (sup s))
          then (rule2 b1 b2 b3 (unique (newt : tt)) ss)
          else rule2 b1 b2 b3 tt ss
        where
          newt = self s `Implies` Exist b2 b3
  Exist c1 c2 `Implies` c3 ->
    if suc a b ssc
      then True --R3
      else
        if r3 /= ssc
          then check tsc tsc r3 a b
          else check tsc ts ssc a b
    where
      r3 = rule3 c1 c2 c3 test ssc
      test = ex tsc
      ex [] = []
      ex (t : tt) = case t of
        x `Implies` Exist c1 y -> (x, y) : (ex tt)
        _ -> ex tt
      rule3 _ _ _ [] ss = ss
      rule3 c1 c2 c3 (t : tt) ss =
        if added /= ss
          then rule3 c1 c2 c3 tt added
          else rule3 c1 c2 c3 tt ss
        where
          added =
            if ok c2 (snd (t)) ss
              then add c3 (fst (t)) ss
              else ss
          ok _ _ [] = False
          ok c2 y (s : ss) = y == (self s) && c2 `elem` (sup s) || ok c2 y ss
          add _ _ [] = []
          add c3 x (s : ss) =
            if (x == (self s))
              then s {sup = unique (c3 : (sup s))} : add c3 x ss
              else s : add c3 x ss
  d1 `Implies` d2 ->
    if added /= ssc
      then check tsc tsc added a b
      else check tsc ts ssc a b
    where
      added = add d1 d2 ssc
      add _ _ [] = []
      add d1 d2 (s : ss) =
        if d1 == self s
          then s {sup = unique (d2 : sup s)} : add d1 d2 ss
          else s : add d1 d2 ss

suc :: Concept -> Concept -> [Super] -> Bool
suc a b [] = False
suc a b (s : ss) = ((self s) == a && b `elem` (sup s)) || suc a b ss

--定义运算符的优先级
infixl 4 `Implies`

infixl 4 `Equivalence`

infixl 6 `Conjunction`

infixr 7 `Exist`

main = do
  let a = Concept "A"
      b = Concept "B"
      c = Concept "C"
      d = Concept "D"
      e = Concept "E"
      r = Role "R"
      s = Role "S"
      oneTBox = [a `Implies` b `Conjunction` r `Exist` c, c `Implies` s `Exist` d, r `Exist` s `Exist` Top `Conjunction` b `Implies` d]

  putStrLn "Logic for Applications"
  print (run oneTBox a d)
