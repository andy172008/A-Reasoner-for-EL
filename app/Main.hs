--author:SX1916085 贺星宇
--github：https://github.com/andy172008/A-Reasoner-for-EL
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
  --这里可以应用第一条normalisation rule
  a `Equivalence` b -> [a `Implies` b, b `Implies` a]
  --这里可以应用第六条normalisation rule
  a `Implies` (b `Conjunction` c) -> [a `Implies` b, a `Implies` c]
  a `Implies` b ->
    --这里可以应用第二条normalisation rule
    if isComplex a && isComplex b
      then [a `Implies` Concept ("new" ++ show i), Concept ("new" ++ show i) `Implies` b]
      else --这里可以应用第三条和第四条normalisation rule

        if isComplex a
          then [fst (divideByTuple i a) `Implies` Concept ("new" ++ show i), snd (divideByTuple i a) `Implies` b]
          else --这里可以应用第五条normalisation rule

            if isComplex b
              then [a `Implies` snd (divideByTuple i b), Concept ("new" ++ show i) `Implies` fst (divideByTuple i b)]
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
  a `Conjunction` b -> isComplexOneConcept a || isComplexOneConcept b
  _ `Exist` a -> isComplexOneConcept a
  _ -> False

--为了完善isComplex的一个工具函数
isComplexOneConcept :: Concept -> Bool
isComplexOneConcept concept = case concept of
  Conjunction _ _ -> True
  Exist _ _ -> True
  _ -> False

--将一个concept进行切割，便于其他函数调用
divideByTuple :: Int -> Concept -> (Concept, Concept)
divideByTuple i concept = case concept of
  a `Exist` b -> (b, a `Exist` Concept ("new" ++ show i))
  a `Conjunction` b ->
    if isComplexOneConcept a
      then (a, Conjunction (Concept ("new" ++ show i)) b)
      else (b, Conjunction (Concept ("new" ++ show i)) a)

--由一个TBox得到一个对应的Super列表
getSuperListByTbox :: TBox -> [Super]
getSuperListByTbox tbox = init (unique (getConeptListByTBox tbox))
  where
    init [] = []
    init (c : others) = Super c [c, Top] : init others

--将TBox中的concept提取出来，构成一个概念列表
getConeptListByTBox :: TBox -> [Concept]
getConeptListByTBox [] = []
getConeptListByTBox (t : ts) = getConceptListByAxiom t ++ getConeptListByTBox ts

--将公理中的concept提取出来，返回一个概念列表
getConceptListByAxiom :: Axiom -> [Concept]
getConceptListByAxiom (a `Implies` b) = extr a ++ extr b
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

--主体函数，main函数直接调用这个函数就能完成功能
runReasoner :: TBox -> Concept -> Concept -> Bool
runReasoner ts = isImplied norms norms supers
  where
    norms = normalisation 1 ts
    supers = getSuperListByTbox norms

--这个函数通过三条规则来检查两个概念是否有包含关系
isImplied :: TBox -> TBox -> [Super] -> Concept -> Concept -> Bool
isImplied _ [] superList a b = suc a b superList
isImplied tsc (t : ts) superList a b = case t of
  Conjunction a1 a2 `Implies` a3 ->
    suc a b superList
      || (if r1 /= superList then isImplied tsc tsc r1 a b else isImplied tsc ts superList a b)
    where
      --定义第一条规则
      r1 = rule1 a1 a2 a3 superList
      rule1 _ _ _ [] = []
      rule1 a1 a2 a3 (s : ss) =
        if a1 `elem` sup s && a2 `elem` sup s
          then s {sup = unique (a3 : sup s)} : rule1 a1 a2 a3 ss
          else s : rule1 a1 a2 a3 ss
  b1 `Implies` Exist b2 b3 ->
    suc a b superList
      || ( if r2 /= tsc
             then isImplied r2 r2 superList a b
             else isImplied tsc ts superList a b
         )
    where
      --定义第二条规则
      r2 = unique (rule2 b1 b2 b3 tsc superList)
      rule2 _ _ _ tt [] = tt
      rule2 b1 b2 b3 tt (s : ss) =
        if b1 `elem` sup s
          then rule2 b1 b2 b3 (unique (newt : tt)) ss
          else rule2 b1 b2 b3 tt ss
        where
          newt = self s `Implies` Exist b2 b3
  Exist c1 c2 `Implies` c3 ->
    suc a b superList
      || ( if r3 /= superList
             then isImplied tsc tsc r3 a b
             else isImplied tsc ts superList a b
         )
    where
      --定义第三条规则
      r3 = rule3 c1 c2 c3 test superList
      test = ex tsc
      ex [] = []
      ex (t : tt) = case t of
        x `Implies` Exist c1 y -> (x, y) : ex tt
        _ -> ex tt
      rule3 _ _ _ [] ss = ss
      rule3 c1 c2 c3 (t : tt) ss =
        if added /= ss
          then rule3 c1 c2 c3 tt added
          else rule3 c1 c2 c3 tt ss
        where
          added =
            if ok c2 (snd t) ss
              then add c3 (fst t) ss
              else ss
          ok _ _ [] = False
          ok c2 y (s : ss) = y == self s && c2 `elem` sup s || ok c2 y ss
          add _ _ [] = []
          add c3 x (s : ss) =
            if x == self s
              then s {sup = unique (c3 : sup s)} : add c3 x ss
              else s : add c3 x ss
  d1 `Implies` d2 ->
    if added /= superList
      then isImplied tsc tsc added a b
      else isImplied tsc ts superList a b
    where
      added = add d1 d2 superList
      add _ _ [] = []
      add d1 d2 (s : ss) =
        if d1 == self s
          then s {sup = unique (d2 : sup s)} : add d1 d2 ss
          else s : add d1 d2 ss

--服务于check函数的工具函数
suc :: Concept -> Concept -> [Super] -> Bool
suc a b [] = False
suc a b (s : ss) = (self s == a && b `elem` sup s) || suc a b ss

--定义运算符的优先级
infixl 4 `Implies`

infixl 4 `Equivalence`

infixl 6 `Conjunction`

infixr 7 `Exist`

main = do
  --定义题目中的概念和关系
  let a = Concept "A"
      b = Concept "B"
      c = Concept "C"
      d = Concept "D"
      e = Concept "E"
      r = Role "R"
      s = Role "S"
      --定义题目中的TBox
      oneTBox = [a `Implies` b `Conjunction` r `Exist` c, c `Implies` s `Exist` d, r `Exist` s `Exist` Top `Conjunction` b `Implies` d]

  putStrLn "Logic for Applications"
  if runReasoner oneTBox a d then print "A is implied in D" else print "A is not implied in D"
