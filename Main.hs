module Main where

import System.Environment (getArgs)
import System.IO (hSetBuffering, stdout, BufferMode(NoBuffering))

import Debug.Trace


-- TODO implement MkSpanPi
data Term = DB Int | StarTm | ZeroTm | OneTm | TwoElim Type Term Term Term
  | DPair Type Type Term Term | Prj1 Type Type Term | Prj2 Type Type Term
  | Lam Type Type Term | App Type Type Term Term
  | C Type
  | Ap Type Type Term Term
  | Apd Type Type Term Term
  | Unspan Type Type Term
  | KZero Type Term
  | S Type Term
  | DummyTm Type Term -- cf. type Dummy below
  deriving (Eq, Read, Show)

data Type = One | Two | Sigma Type Type | Pi Type Type | U | El Term
  | Span Type
  | DSpan Type Type Term
  | Dummy Type Term -- simple alternative for strict Eq
  deriving (Eq, Read, Show)

type Ctx = [Type]

type Subst = Term

data TypeFold a b = TypeFold {
-- terms
  db :: Int -> b
, starTm :: b
, zeroTm :: b
, oneTm :: b
, twoElim :: a -> b -> b -> b -> b
, dPair :: a -> a -> b -> b -> b
, prj1 :: a -> a -> b -> b
, prj2 :: a -> a -> b -> b
, lam :: a -> a -> b -> b
, app :: a -> a -> b -> b -> b
, c :: a -> b
, ap :: a -> a -> b -> b -> b
, apd :: a -> a -> b -> b -> b
, unspan :: a -> a -> b -> b
, kZero :: a -> b -> b
, s :: a -> b -> b
, dummyTm :: a -> b -> b
-- types
, one :: a
, two :: a
, sigma :: a -> a -> a
, pi :: a -> a -> a
, u :: a
, el :: b -> a
, span :: a -> a
, dSpan :: a -> a -> b -> a
, dummy :: a -> b -> a
}

idTypeFold :: TypeFold Type Term
idTypeFold = TypeFold
  DB StarTm ZeroTm OneTm TwoElim DPair Prj1 Prj2 Lam App C Ap Apd Unspan KZero S DummyTm
  One Two Sigma Pi U El Span DSpan Dummy

binTypeFold :: (a -> a -> a) -> a -> (Int -> a) -> TypeFold a a
binTypeFold bn a f = TypeFold
  f a a a bn4 bn4 bn3 bn3 bn3 bn4 bn1 bn4 bn4 bn3 bn2 bn2 bn2 a a bn2 bn2 a bn1 bn1 bn3 bn2
  where
    bn1 = bn2 a
    bn2 = bn3 a
    bn3 = bn4 a
    bn4 x1 x2 x3 x4 = bn x1 (bn x2 (bn x3 x4))

foldType :: (Int -> TypeFold a b) -> Type -> a
foldType f One = one (f 0)
foldType f Two = two (f 0)
foldType f (Sigma t' t) = sigma (f 0) (foldType f t') (foldType (f . (+1)) t)
foldType f (Pi t' t) = Main.pi (f 0) (foldType f t') (foldType (f . (+1)) t)
foldType f U = u (f 0)
foldType f (El tm) = el (f 0) (foldTerm f tm)
foldType f (Span t) = Main.span (f 0) (foldType f t)
foldType f (DSpan t' t a) = dSpan (f 0) (foldType f t') (foldType (f . (+1)) t) (foldTerm f a)
foldType f (Dummy t tm) = dummy (f 0) (foldType f t) (foldTerm f tm)

foldTerm :: (Int -> TypeFold a b) -> Term -> b
foldTerm f (DB m) = db (f 0) m
foldTerm f StarTm = starTm (f 0)
foldTerm f ZeroTm = zeroTm (f 0)
foldTerm f OneTm = oneTm (f 0)
foldTerm f (TwoElim t tm u v) = twoElim (f 0) (foldType f t) (foldTerm f tm) (foldTerm f u) (foldTerm f v)
foldTerm f (DPair t' t u v) = dPair (f 0) (foldType f t') (foldType (f . (+1)) t) (foldTerm f u) (foldTerm f v)
foldTerm f (Prj1 t' t tm) = prj1 (f 0) (foldType f t') (foldType (f . (+1)) t) (foldTerm f tm)
foldTerm f (Prj2 t' t tm) = prj2 (f 0) (foldType f t') (foldType (f . (+1)) t) (foldTerm f tm)
foldTerm f (Lam t' t tm) = lam (f 0) (foldType f t') (foldType (f . (+1)) t) (foldTerm (f . (+1)) tm)
foldTerm f (App t' t fn tm) = app (f 0) (foldType f t') (foldType (f . (+1)) t) (foldTerm f fn) (foldTerm f tm)
foldTerm f (C t) = c (f 0) (foldType f t)
foldTerm f (Ap t t' tm a) = ap (f 0) (foldType f t) (foldType f t') (foldTerm (f . (+1)) tm) (foldTerm f a)
foldTerm f (Apd t t' tm a) = apd (f 0) (foldType f t) (foldType (f . (+1)) t') (foldTerm (f . (+1)) tm) (foldTerm f a)
foldTerm f (Unspan t0 t tm) = unspan (f 0) (foldType f t0) (foldType f t) (foldTerm (f . (+1)) tm)
foldTerm f (KZero t tm) = kZero (f 0) (foldType f t) (foldTerm f tm)
foldTerm f (S t tm) = s (f 0) (foldType f t) (foldTerm f tm)
foldTerm f (DummyTm t tm) = dummyTm (f 0) (foldType f t) (foldTerm f tm)

mapTypeFold :: (Int -> Int -> Term) -> Int -> TypeFold Type Term
mapTypeFold f n = idTypeFold { db = \m -> f m n }

mapType :: (Int -> Int -> Term) -> Type -> Type
mapType f t = foldType (mapTypeFold f) t

mapTerm :: (Int -> Int -> Term) -> Term -> Term
mapTerm f t = foldTerm (mapTypeFold f) t

substAuxFct :: Subst -> Int -> Int -> Term
substAuxFct s m n = if m == n then (moveIndicesTm n s) else (if m > n then (DB (m-1)) else (DB m))

subst :: Type -> Subst -> Type
subst t s = mapType (substAuxFct s) t

substTm :: Term -> Subst -> Term
substTm tm s = mapTerm (substAuxFct s) tm

containsDB0 :: Type -> Bool
containsDB0 = foldType (\n -> binTypeFold (||) False (==n))

reduceTm :: Term -> Term
reduceTm (TwoElim t tm u v)
  | reduceTm tm == ZeroTm = reduceTm u
  | reduceTm tm == OneTm  = reduceTm v
  | otherwise = TwoElim (reduce t) (reduceTm tm) (reduceTm u) (reduceTm v)
reduceTm (DPair t' t u v) = DPair (reduce t') (reduce t) (reduceTm u) (reduceTm v)
reduceTm (Prj1 t' t tm) =
  case reduceTm tm of
    DPair _ _ u _ -> reduceTm u
    -- ----
    -- attempt to get closer to normalization (instance of the inverse dir. of the eq. implemented below)
    tm'@(Apd _ _ _ (DPair _ _ (Unspan _ _ _) _)) ->
      reduceTm
        (Prj2 U (El (DB 0))
          (KZero (Sigma U (El (DB 0))) (DPair (Span U) (Sigma t' t) (Unspan t' (Sigma t' t) (Prj1 t' t (DB 0))) tm')))
    -- TODO (maybe): similar rule for Prj2 ?
    -- ----
    tm' -> Prj1 (reduce t') (reduce t) tm'
reduceTm (Prj2 t' t tm) =
  case reduceTm tm of
    DPair _ _ _ v -> reduceTm v
    -- ----
    -- counterpart to the attempt to get closer to normalization above:
    --   excludes this case to avoid the loop and adds a special reduction rule (see TODO)
    tm'@(KZero (Sigma U (El (DB 0))) (DPair (Span U) U (Unspan _ _ tm2) (Apd _ _ _ (DPair _ _ (Unspan _ _ _) _)))) ->
      Prj2 (reduce t') (reduce t) tm' -- TODO: the special reduction in this case (cf. page 14 of the paper: second eq.)
    -- ----
    KZero (Sigma U (El (DB 0))) (DPair (Span U) U (Unspan _ _ tm2) a) -> reduceTm (substTm tm2 a) -- for kd
    tm' -> Prj2 (reduce t') (reduce t) tm'
reduceTm (App t' t f tm) =
  case reduceTm f of Lam _ _ tm' -> substTm tm' (reduceTm tm); tm' -> App (reduce t') (reduce t) tm' (reduceTm tm)
reduceTm (C t) = case reduce t of El tm -> tm; t' -> C t'
reduceTm (Ap _ _ (DB 0) a) = reduceTm a
reduceTm (Ap t _ (DPair t'1 t'2 u v) a) =
  DPair (reduce (Span t'1)) (reduce (DSpan t (subst t'2 u) a)) (reduceTm (Ap t t'1 u a)) (reduceTm (Apd t t'2 v a))
-- not in the paper b/c covered by the DPair eq. above + eta law, but we do not have eta in our red. rules
reduceTm (Ap t0' _ (Prj1 t' t tm) a) = reduceTm (Prj1 (Span t') (DSpan t' t (DB 0)) (Ap t0' (Sigma t' t) tm a))
-- not in the paper b/c covered by the DPair eq. above + eta law, but we do not have eta in our red. rules
reduceTm (Ap t0' _ (Prj2 t' t tm) a) = reduceTm (Prj2 (Span t') (DSpan t' t (DB 0)) (Ap t0' (Sigma t' t) tm a))
reduceTm (Ap _ _ StarTm _) = StarTm -- not in the paper b/c covered by the eta law, but we do not have these in our red. rules
reduceTm (Ap _ _ ZeroTm _) = ZeroTm
reduceTm (Ap _ _ OneTm _) = OneTm
reduceTm (Ap t t' g a) =
  case reduceTm a of
    Ap t2 _ f a' -> reduceTm (Ap t2 t' (substTm g f) a') -- covers the one below
    --Ap t2 _ a' StarTm -> reduceTm (Ap t2 t' (substTm g a') StarTm) -- for R (R A a = Ap One A a StarTm (no (DB 0) in a))
    tm'@(S t2 a') ->
      case g of Ap t3 t3' f (DB 0) -> reduceTm (S t3' (Ap t t' (Ap t3 t3' f (DB 0)) a')); _ -> Ap (reduce t) (reduce t') g tm'
    tm -> Ap (reduce t) (reduce t') g tm
reduceTm (Apd t t' g a)
  | containsDB0 t' =
    case g of
      DPair b c u v ->
        DPair (reduce (DSpan t b a)) (reduce (DSpan t (subst c u) a))
          (reduceTm (Apd t b u a)) (reduceTm (Apd t (subst c u) v a))
      TwoElim t2 tm u v ->
        TwoElim (reduce (DSpan t t2 a)) (reduceTm (Ap t Two tm a))
          (reduceTm (Ap t (subst t2 ZeroTm) u a)) (reduceTm (Ap t (subst t2 OneTm) v a))
      _ ->
        case reduceTm a of Apd t2 _ f a' -> Apd t2 (subst t' f) (substTm g f) a'; tm -> Apd (reduce t) t' g tm
  | otherwise = Ap t t' g a
reduceTm (KZero t tm) =
  case reduceTm tm of
    Ap t2 t2' f a -> reduceTm (substTm f (KZero t2 a)) -- covers the one below
    --Ap t2 _ a StarTm -> reduceTm a -- for R (R A a = Ap One A a StarTm (no (DB 0) in a))
    S t2 a -> reduceTm (Ap (Span t2) t2 (KZero t2 (DB 0)) a)
    tm' -> KZero (reduce t) tm'
reduceTm (S t tm) =
  case reduceTm tm of
    S _ tm2 -> reduceTm tm2
    Ap t2 t2' tm'@(S ta (DB 0)) (S _ a) -> reduceTm (Ap t2 t2' tm' (S (Span ta) (Ap t2 t2' tm' a)))
    Ap t2 _ a StarTm ->
      reduceTm (Ap t (Span t) (Ap One t (DB 0) StarTm) a) -- for R (R A a = Ap One A a StarTm (no (DB 0) in a))
    tm' -> S (reduce t) tm'
reduceTm tm = tm

reduce :: Type -> Type
reduce (Sigma t' t) = Sigma (reduce t') t
reduce (Pi t' t) = Pi (reduce t') t
reduce (El tm) = case reduceTm tm of KZero U (Unspan t0 t tm') -> t0; C t -> reduce t; tm' -> El tm'
reduce (Span t) =
  case reduce t of
    One -> One
    Two -> Two
    Sigma t'0 t0 -> Sigma (reduce (Span t'0)) (DSpan t'0 t0 (DB 0))
    t' -> Span t'
reduce (DSpan t' t a)
  | containsDB0 t =
    case t of
      Sigma b c ->
        Sigma (reduce (DSpan t' b a)) (DSpan (Sigma t' b) c (DPair (Span t') (DSpan t' b a) a (DB 0)))
      El tm0 ->
        case (tm0, reduceTm a) of
          (DB 0, Unspan t20 t2 tm2) -> t2
          -- ----
          -- attempt to get closer to normalization (instance of the inverse dir. of the eq. implemented below)
          (DB 0, tm) -> DSpan (reduce t') t tm
          (_, tm) -> reduce (DSpan U (El (DB 0)) (Ap t' U tm0 tm))
          -- ----
      _ ->
        case reduceTm a of Ap t2 t2' tm a' -> DSpan t2 (subst t tm) a'; tm -> DSpan (reduce t') t tm
  | otherwise = reduce (Span (reduce t))
reduce (Dummy t tm) = Dummy (reduce t) (reduceTm tm)
reduce t = t

moveIndicesFct :: Int -> Int -> Int -> Term
moveIndicesFct n m l = DB (if m >= l then (m+n) else m)

moveIndices :: Int -> Type -> Type
moveIndices n = mapType (moveIndicesFct n)

moveIndicesTm :: Int -> Term -> Term
moveIndicesTm n = mapTerm (moveIndicesFct n)

typecheck :: Ctx -> Type -> Bool
typecheck ctx (Sigma t' t) = (typecheck ctx t') && (typecheck (t':ctx) t)
typecheck ctx (Pi t' t) = (typecheck ctx t') && (typecheck (t':ctx) t)
typecheck ctx (El tm) = typecheckTm ctx tm U
typecheck ctx (Span t) = typecheck ctx t
typecheck ctx (DSpan t' t a) = (typecheck (t':ctx) t) && (typecheckTm ctx a (Span t'))
typecheck _ t = True

inferType :: Ctx -> Term -> Either String Type
inferType ctx (DB n) = if length ctx > n then Right (moveIndices (n+1) (ctx !! n)) else Left "DB"
inferType _ StarTm = Right One
inferType _ ZeroTm = Right Two
inferType _ OneTm = Right Two
inferType ctx (TwoElim t tm u v)
  | (typecheck (Two:ctx) t) && (typecheckTm ctx tm Two) &&
    (typecheckTm ctx u (subst t ZeroTm)) && (typecheckTm ctx v (subst t OneTm))
    = Right (subst t tm)
  | otherwise = Left "TwoElim"
inferType ctx (DPair t' t u v)
  | (typecheckTm ctx u t') && (typecheckTm ctx v (subst t u)) = Right (Sigma t' t)
  | otherwise = Left "DPair"
inferType ctx (Prj1 t' t tm)
  | typecheckTm ctx tm (Sigma t' t) = Right t'
  | otherwise = Left "Prj1"
inferType ctx (Prj2 t' t tm)
  | typecheckTm ctx tm (Sigma t' t) = Right (subst t (Prj1 t' t tm))
  | otherwise = Left "Prj2"
inferType ctx (Lam t' t tm)
  | typecheckTm (t':ctx) tm t = Right (Pi t' t)
  | otherwise = Left "Lam"
inferType ctx (App t' t f tm)
  | (typecheckTm ctx f (Pi t' t)) && (typecheckTm ctx tm t') = Right (subst t tm)
  | otherwise = Left "App"
inferType ctx (C t) = if typecheck ctx t then Right U else Left "C"
inferType ctx (Ap t t' tm a)
  | (typecheck ctx t') && (typecheckTm (t:ctx) tm (moveIndices 1 t')) && (typecheckTm ctx a (Span t)) = Right (Span t')
  | otherwise = Left "Ap"
inferType ctx (Apd t t' tm a)
  | (typecheck (t:ctx) t') && (typecheckTm (t:ctx) tm t') && (typecheckTm ctx a (Span t)) = Right (DSpan t t' a)
  | otherwise = Left "Apd"
inferType ctx (Unspan t0 t tm)
  | (typecheck ctx t0) && (typecheck ctx t) && (typecheckTm (t:ctx) tm (moveIndices 1 t0)) = Right (Span U)
  | otherwise = Left "Unspan"
inferType ctx (KZero t tm) = if typecheckTm ctx tm (Span t) then Right t else Left "KZero"
inferType ctx (S t tm) = if typecheckTm ctx tm (Span (Span t)) then Right (Span (Span t)) else Left "S"
inferType ctx (DummyTm t tm) = if typecheckTm ctx tm t then Right (Dummy t tm) else Left "DummyTm"

typecheckTm :: Ctx -> Term -> Type -> Bool
typecheckTm ctx tm t =
  case inferType ctx tm of
    Right t' -> if reduce t' == reduce t then True else trace (show (reduce t')++"=/="++show (reduce t)) $ False
    Left m -> trace m $ False

typecheckTmWithMsg :: Ctx -> Term -> Type -> Either String ()
typecheckTmWithMsg ctx tm t =
  case inferType ctx tm of
    Right t' -> if reduce t' == reduce t then Right () else Left "Inferred type does not match."
    Left m -> Left ("Inference error at: "++m)

prettyTm :: Term -> Bool -> String
prettyTm (DB n) s = "\ESC[34m"++show n++"\ESC[37m"
prettyTm StarTm s = "\x2605"
prettyTm ZeroTm s = "0\x2082"
prettyTm OneTm s = "1\x2082"
prettyTm (TwoElim t tm u v) s = "ind\x2082\x27E8"++pretty t s++"\x27E9("++prettyTm tm s++", "++prettyTm u s++", "++prettyTm v s++")"
prettyTm (DPair t' t u v) s = "\x27E8"++pretty t' s++"."++pretty t s++"\x27E9("++prettyTm u s++", "++prettyTm v s++")"
prettyTm (Prj1 t' t tm) False = "π\x2081\x27E8"++pretty t' False++"."++pretty t False++"\x27E9 "++prettyTm tm False
prettyTm (Prj1 t' t tm) True = "π\x2081 "++prettyTm tm True
prettyTm (Prj2 t' t tm) False = "π\x2082\x27E8"++pretty t' False++"."++pretty t False++"\x27E9 "++prettyTm tm False
prettyTm (Prj2 t' t tm) True = "π\x2082 "++prettyTm tm True
prettyTm (Lam t' t tm) False = "\\\x27E8"++pretty t' False++"."++pretty t False++"\x27E9 {"++prettyTm tm False++"}"
prettyTm (Lam t' t tm) True = "\\{"++prettyTm tm True++"}"
prettyTm (App t' t f tm) False = "app\x27E8"++pretty t' False++"."++pretty t False++"\x27E9("++prettyTm f False++", "++prettyTm tm False++")"
prettyTm (App t' t f tm) True = "app("++prettyTm f True++", "++prettyTm tm True++")"
prettyTm (C t) s = "c "++pretty t s
prettyTm (Ap t t' tm a) s  = "ap("++pretty t s++"."++prettyTm tm s++":"++pretty t' s++")("++prettyTm a s++")"
prettyTm (Apd t t' tm a) s = "apd("++pretty t s++"."++prettyTm tm s++":"++pretty t' s++")("++prettyTm a s++")"
prettyTm (Unspan t0 t tm) s = "unspan("++pretty t0 s++", "++pretty t s++"."++prettyTm tm s++")"
prettyTm (KZero t tm) s = "k\x27E8"++pretty t s++"\x27E9("++prettyTm tm s++")"
prettyTm (S t tm) s = "S\x27E8"++pretty t s++"\x27E9("++prettyTm tm s++")"
prettyTm (DummyTm _ _) _ = "D"

pretty :: Type -> Bool -> String
pretty One s = "\ESC[1m1\ESC[0m"
pretty Two s = "\ESC[1m2\ESC[0m"
pretty (Sigma t' t) s = "∑"++pretty t' s++"."++pretty t s
pretty (Pi t' t) s = "∏"++pretty t' s++"."++pretty t s
pretty U s = "\ESC[1mU\ESC[0m"
pretty (El tm) s = "El("++prettyTm tm s++")"
pretty (Span t) s = "\x2200"++pretty t s
pretty (DSpan t' t a) s = "\x2200"++"d("++pretty t' s++"."++pretty t s++")("++prettyTm a s++")"
pretty (Dummy t tm) False = "D\x27E8"++pretty t False++"\x27E9("++prettyTm tm False++")"
pretty (Dummy _ tm) True = "D("++prettyTm tm False++")"

-- simplified by special-casing to type A = Two and predicate (x : A) |- P = (Dummy A x)
idFctParametricity :: Type
idFctParametricity =
  Pi (Pi (Sigma U (El (DB 0))) (El (Prj1 U (El (DB 0)) (DB 0))))
    (Pi Two
      (Pi (Dummy Two (DB 0))
        (Dummy Two
          (App (Sigma U (El (DB 0))) (El (Prj1 U (El (DB 0)) (DB 0)))
            (DB 2) (DPair U (El (DB 0)) (C Two) (DB 1))))
      ))

idFctParametricityTm :: Term
idFctParametricityTm =
  case idFctParametricity of
    Pi i o@(Pi i2 o2@(Pi i3 o3)) ->
      Lam i o (Lam i2 o2 (Lam i3 o3
        (Prj2 Two (Dummy Two (DB 0))
          (idFctParametricityTmAux 2 1 0))
      ))
    _ -> undefined

-- idFctParametricity without Prj2 around it
idFctParametricityPart1 :: Type
idFctParametricityPart1 =
  Pi (Pi (Sigma U (El (DB 0))) (El (Prj1 U (El (DB 0)) (DB 0))))
    (Pi Two
      (Pi (Dummy Two (DB 0))
        (Sigma Two (Dummy Two (DB 0)))
      ))

idFctParametricityPart1Tm :: Term
idFctParametricityPart1Tm =
  case idFctParametricityPart1 of
    Pi i o@(Pi i2 o2@(Pi i3 o3)) ->
      Lam i o (Lam i2 o2 (Lam i3 o3
        (idFctParametricityTmAux 2 1 0)
      ))
    _ -> undefined

idFctParametricityTmAux :: Int -> Int -> Int -> Term
idFctParametricityTmAux f a p =
  Apd (Sigma U (El (DB 0))) (El (Prj1 U (El (DB 0)) (DB 0)))
    (App (Sigma U (El (DB 0))) (El (Prj1 U (El (DB 0)) (DB 0))) (DB (f+1)) (DB 0))
    (DPair (Span U) (DSpan U (El (DB 0)) (DB 0))
      (Unspan Two (Sigma Two (Dummy Two (DB 0)))
        (Prj1 Two (Dummy Two (DB 0)) (DB 0)))
      (DPair Two (Dummy Two (DB 0)) (DB a) (DB p)))

-- Prj1 of idFctParametricityPart1Tm, wrapped with Dummy to see the inner reduction works
idFctParametricityPart2Tm :: Term
idFctParametricityPart2Tm =
  case idFctParametricityPart2 of
    Pi i o@(Pi i2 o2@(Pi i3 o3)) ->
      Lam i o (Lam i2 o2 (Lam i3 o3
        (DummyTm Two (Prj1 Two (Dummy Two (DB 0)) (idFctParametricityTmAux 2 1 0)))
      ))
    _ -> undefined

idFctParametricityPart2 :: Type
idFctParametricityPart2 =
  Pi (Pi (Sigma U (El (DB 0))) (El (Prj1 U (El (DB 0)) (DB 0))))
    (Pi Two
      (Pi (Dummy Two (DB 0))
        (Dummy Two
          (App (Sigma U (El (DB 0))) (El (Prj1 U (El (DB 0)) (DB 0)))
            (DB 2) (DPair U (El (DB 0)) (C Two) (DB 1))))
      ))

main :: IO ()
main = do
  args <- getArgs
  let simplePp = args == ["-s"] -- simplified pretty printing
  hSetBuffering stdout NoBuffering
  putStr "Term: "
  tmS <- getLine
  let tm = if tmS == "idFctParametricityPart1Tm" then idFctParametricityPart1Tm else read tmS
  putStr "Type: "
  tS <- getLine
  let t = if tS == "idFctParametricityPart1" then idFctParametricityPart1 else read tS
  putStrLn "_________________________________"
  let t' = reduce t
  let res = typecheckTmWithMsg [] tm t
  putStrLn (pretty t simplePp ++ " \x21A0 " ++ pretty t' simplePp)
  putStrLn "_________________________________"
  putStrLn (prettyTm tm simplePp ++ " : " ++ pretty t simplePp ++ (if res == Right () then " \ESC[32m\x2713" else " \ESC[31m\x2717"))
  case res of
    Right () -> putStrLn ("\ESC[37m" ++ prettyTm tm simplePp ++ " \x21A0 " ++ prettyTm (reduceTm tm) simplePp)
    Left m -> putStrLn m
