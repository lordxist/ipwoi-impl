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
  | DummyTm -- cf. type Dummy below
  deriving (Eq, Read, Show)

data Type = One | Two | Sigma Type Type | Pi Type Type | U | El Term
  | Span Type
  | DSpan Type Type Term
  | Dummy Type Term -- simple alternative for strict Eq
  deriving (Eq, Read, Show)

type Ctx = [Type]

type Subst = Term

mapType :: (Term -> a -> Int -> Term) -> Type -> a -> Int -> Type
mapType f (Sigma t' t) s n = Sigma (mapType f t' s n) (mapType f t s (n+1))
mapType f (Pi t' t) s n = Pi (mapType f t' s n) (mapType f t s (n+1))
mapType f (El tm) s n = El (f tm s n)
mapType f (Span t) s n = Span (mapType f t s n)
mapType f (DSpan t' t a) s n = DSpan (mapType f t' s n) (mapType f t s (n+1)) (f a s n)
mapType _ t _ _ = t

substAux :: Type -> Subst -> Int -> Type
substAux = mapType substAuxTm

substAuxTm :: Term -> Subst -> Int -> Term
substAuxTm (DB m) s n = if m == n then (moveIndicesTm s n 0) else (if m > n then (DB (m-1)) else (DB m))
substAuxTm (TwoElim t tm u v) s n = TwoElim (substAux t s n) (substAuxTm tm s n) (substAuxTm u s n) (substAuxTm v s n)
substAuxTm (DPair t' t u v) s n = DPair (substAux t' s n) (substAux t s (n+1)) (substAuxTm u s n) (substAuxTm v s n)
substAuxTm (Prj1 t' t tm) s n = Prj1 (substAux t' s n) (substAux t s (n+1)) (substAuxTm tm s n)
substAuxTm (Prj2 t' t tm) s n = Prj2 (substAux t' s n) (substAux t s (n+1)) (substAuxTm tm s n)
substAuxTm (Lam t' t tm) s n = Lam (substAux t' s n) (substAux t s (n+1)) (substAuxTm tm s (n+1))
substAuxTm (App t' t f tm) s n = App (substAux t' s n) (substAux t s (n+1)) (substAuxTm f s n) (substAuxTm tm s n)
substAuxTm (C t) s n = C (substAux t s n)
substAuxTm (Ap t t' tm a) s n = Ap (substAux t s n) (substAux t' s n) (substAuxTm tm s (n+1)) (substAuxTm a s n)
substAuxTm (Apd t t' tm a) s n = Apd (substAux t s n) (substAux t' s (n+1)) (substAuxTm tm s (n+1)) (substAuxTm a s n)
substAuxTm (Unspan t0 t tm) s n = Unspan (substAux t0 s n) (substAux t s n) (substAuxTm tm s (n+1))
substAuxTm (KZero t tm) s n = KZero (substAux t s n) (substAuxTm tm s n)
substAuxTm (S t tm) s n = S (substAux t s n) (substAuxTm tm s n)
substAuxTm tm _ _ = tm

subst :: Type -> Subst -> Type
subst t s = substAux t s 0

substTm :: Term -> Subst -> Term
substTm tm s = substAuxTm tm s 0

containsDB0Tm :: Term -> Int -> Bool
containsDB0Tm (DB m) n = m == n
containsDB0Tm (TwoElim t tm u v) n = (containsDB0 t n) || (containsDB0Tm tm n) || (containsDB0Tm u n) || (containsDB0Tm v n)
containsDB0Tm (DPair t' t u v) n = (containsDB0 t' n) || (containsDB0 t (n+1)) || (containsDB0Tm u n) || (containsDB0Tm v n)
containsDB0Tm (Prj1 t' t tm) n = (containsDB0 t' n) || (containsDB0 t (n+1)) || (containsDB0Tm tm n)
containsDB0Tm (Prj2 t' t tm) n = (containsDB0 t' n) || (containsDB0 t (n+1)) || (containsDB0Tm tm n)
containsDB0Tm (Lam t' t tm) n = (containsDB0 t' n) || (containsDB0 t (n+1)) || (containsDB0Tm tm (n+1))
containsDB0Tm (App t' t f tm) n = (containsDB0 t' n) || (containsDB0 t (n+1)) || (containsDB0Tm f n) || (containsDB0Tm tm n)
containsDB0Tm (C t) n = containsDB0 t n
containsDB0Tm (Ap t t' tm a) n = (containsDB0 t n) || (containsDB0 t' n) || (containsDB0Tm tm (n+1)) || (containsDB0Tm a n)
containsDB0Tm (Apd t t' tm a) n = (containsDB0 t n) || (containsDB0 t' (n+1)) || (containsDB0Tm tm (n+1)) || (containsDB0Tm a n)
containsDB0Tm (Unspan t0 t tm) n = (containsDB0 t0 n) || (containsDB0 t n) || (containsDB0Tm tm (n+1))
containsDB0Tm (KZero t tm) n = (containsDB0 t n) || (containsDB0Tm tm n)
containsDB0Tm (S t tm) n = (containsDB0 t n) || (containsDB0Tm tm n)
containsDB0Tm _  _ = False

containsDB0 :: Type -> Int -> Bool
containsDB0 (Sigma t' t) n = (containsDB0 t' n) || (containsDB0 t (n+1))
containsDB0 (Pi t' t) n = (containsDB0 t' n) || (containsDB0 t (n+1))
containsDB0 (El tm) n = containsDB0Tm tm n
containsDB0 (Span t) n = containsDB0 t n
containsDB0 (DSpan t' t a) n = (containsDB0 t' n) || (containsDB0 t (n+1)) || (containsDB0Tm a n)
containsDB0 _ _ = False

reduceTm :: Term -> Term
reduceTm (TwoElim t tm u v)
  | reduceTm tm == ZeroTm = reduceTm u
  | reduceTm tm == OneTm  = reduceTm v
  | otherwise = TwoElim (reduce t) (reduceTm tm) (reduceTm u) (reduceTm v)
reduceTm (DPair t' t u v) = DPair (reduce t') (reduce t) (reduceTm u) (reduceTm v)
reduceTm (Prj1 t' t tm) = case reduceTm tm of DPair _ _ u _ -> reduceTm u; tm' -> Prj1 (reduce t') (reduce t) tm'
reduceTm (Prj2 t' t tm) =
  case reduceTm tm of
    DPair _ _ _ v -> reduceTm v
    KZero (Sigma U (El (DB 0))) (DPair (Span U) U (Unspan _ _ tm2) a) -> reduceTm (substTm tm2 a) -- for kd
    tm' -> Prj2 (reduce t') (reduce t) tm'
reduceTm (App t' t f tm) =
  case reduceTm f of Lam _ _ tm' -> substTm tm' (reduceTm tm); tm' -> App (reduce t') (reduce t) tm' (reduceTm tm)
reduceTm (C t) = case reduce t of El tm -> tm; t' -> C t'
reduceTm (Ap _ _ (DB 0) a) = reduceTm a
reduceTm (Ap t _ (DPair t'1 t'2 u v) a) =
  DPair (reduce (Span t'1)) (reduce (DSpan t (subst t'2 u) a)) (reduceTm (Ap t t'1 u a)) (reduceTm (Apd t t'2 v a))
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
  | containsDB0 t' 0 =
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
  | containsDB0 t 0 =
    case t of
      Sigma b c ->
        Sigma (reduce (DSpan t' b a)) (DSpan (Sigma t' b) c (DPair (Span t') (DSpan t' b a) a (DB 0)))
      El (DB 0) ->
        case reduceTm a of Unspan t20 t2 tm2 -> t2; tm -> DSpan (reduce t') t tm
      _ ->
        case reduceTm a of Ap t2 t2' tm a' -> DSpan t2 (subst t tm) a'; tm -> DSpan (reduce t') t tm
  | otherwise = reduce (Span (reduce t))
reduce t = t

moveIndices :: Type -> Int -> Int -> Type
moveIndices = mapType moveIndicesTm

moveIndicesTm :: Term -> Int -> Int -> Term
moveIndicesTm (DB m) n l = DB (if m >= l then (m+n) else m)
moveIndicesTm (TwoElim t tm u v) n l = TwoElim (moveIndices t n l) (moveIndicesTm tm n l) (moveIndicesTm u n l) (moveIndicesTm v n l)
moveIndicesTm (DPair t' t u v) n l = DPair (moveIndices t' n l) (moveIndices t n (l+1)) (moveIndicesTm u n l) (moveIndicesTm v n l)
moveIndicesTm (Prj1 t' t tm) n l = Prj1 (moveIndices t' n l) (moveIndices t n (l+1)) (moveIndicesTm tm n l)
moveIndicesTm (Prj2 t' t tm) n l = Prj2 (moveIndices t' n l) (moveIndices t n (l+1)) (moveIndicesTm tm n l)
moveIndicesTm (Lam t' t tm) n l = Lam (moveIndices t' n l) (moveIndices t n (l+1)) (moveIndicesTm tm n (l+1))
moveIndicesTm (App t' t f tm) n l = App (moveIndices t' n l) (moveIndices t n (l+1)) (moveIndicesTm f n l) (moveIndicesTm tm n l)
moveIndicesTm (C t) n l = C (moveIndices t n l)
moveIndicesTm (Ap t t' tm a) n l = Ap (moveIndices t n l) (moveIndices t' n l) (moveIndicesTm tm n (l+1)) (moveIndicesTm a n l)
moveIndicesTm (Apd t t' tm a) n l = Apd (moveIndices t n l) (moveIndices t' n (l+1)) (moveIndicesTm tm n (l+1)) (moveIndicesTm a n l)
moveIndicesTm (Unspan t0 t tm) n l = Unspan (moveIndices t0 n l) (moveIndices t n l) (moveIndicesTm tm n (l+1))
moveIndicesTm (KZero t tm) n l = KZero (moveIndices t n l) (moveIndicesTm tm n l)
moveIndicesTm (S t tm) n l = S (moveIndices t n l) (moveIndicesTm tm n l)
moveIndicesTm tm _ _ = tm

typecheck :: Ctx -> Type -> Bool
typecheck ctx (Sigma t' t) = (typecheck ctx t') && (typecheck (t':ctx) t)
typecheck ctx (Pi t' t) = (typecheck ctx t') && (typecheck (t':ctx) t)
typecheck ctx (El tm) = typecheckTm ctx tm U
typecheck ctx (Span t) = typecheck ctx t
typecheck ctx (DSpan t' t a) = (typecheck (t':ctx) t) && (typecheckTm ctx a (Span t'))
typecheck _ t = True

inferType :: Ctx -> Term -> Either String Type
inferType ctx (DB n) = if length ctx > n then Right (moveIndices (ctx !! n) (n+1) 0) else Left "DB"
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
  | (typecheck ctx t') && (typecheckTm (t:ctx) tm (moveIndices t' 1 0)) && (typecheckTm ctx a (Span t)) = Right (Span t')
  | otherwise = Left "Ap"
inferType ctx (Apd t t' tm a)
  | (typecheck (t:ctx) t') && (typecheckTm (t:ctx) tm t') && (typecheckTm ctx a (Span t)) = Right (DSpan t t' a)
  | otherwise = Left "Apd"
inferType ctx (Unspan t0 t tm)
  | (typecheck ctx t0) && (typecheck ctx t) && (typecheckTm (t:ctx) tm (moveIndices t0 1 0)) = Right (Span U)
  | otherwise = Left "Unspan"
inferType ctx (KZero t tm) = if typecheckTm ctx tm (Span t) then Right t else Left "KZero"
inferType ctx (S t tm) = if typecheckTm ctx tm (Span (Span t)) then Right (Span (Span t)) else Left "S"

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
prettyTm DummyTm _ = "D"

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
-- TODO adapt type checking such that this can be typed to (Sigma A P)
-- (find out how to realize this with reduction rules:
--  maybe reverse direction of DSpan/Apd composition rule,
--  but how constructively? -- would need to invent a substitution)
idFctParametricityPart1 :: Type
idFctParametricityPart1 =
  Pi (Pi (Sigma U (El (DB 0))) (El (Prj1 U (El (DB 0)) (DB 0))))
    (Pi Two
      (Pi (Dummy Two (DB 0))
        (DSpan (Sigma U (El (DB 0))) (El (Prj1 U (El (DB 0)) (DB 0)))
          (DPair (Span U) (DSpan U (El (DB 0)) (DB 0))
            (Unspan Two (Sigma Two (Dummy Two (DB 0)))
              (Prj1 Two (Dummy Two (DB 0)) (DB 0)))
            (DPair Two (Dummy Two (DB 0)) (DB 1) (DB 0))))
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
