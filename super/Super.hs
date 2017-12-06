{-# OPTIONS_GHC -fno-warn-tabs #-}


module Super where
import Data.Map
import Data.List
import Data.Set 
import Trace
import Data.Maybe

newtype Var = Var String deriving (Eq, Show)
instance Ord Var  where
    (Var v1) `compare` (Var v2) = 
        let n = length v1 in
        let n2 = length v2 in
        let ret = n `compare` n2 in
        if (ret == EQ) then v1 `compare` v2 else ret

data Constructor e = Constructor String [e] deriving (Eq, Show)
data Sample =  SK (Constructor Var) | SI Int deriving (Eq, Show)
data Lambda = Lambda Var Exp deriving (Eq, Show) 
data CaseSamp =  CaseSamp Sample Exp deriving (Eq, Show) 
data Exp = 
 	Const Int 
 	| LVar Var 
    | GVar Var
 	| Cons (Constructor Exp)
 	| Lam Lambda
 	| App Exp Exp
 	| Case Exp [CaseSamp]
    | Sum Exp Exp
    | Let Var Exp Exp
    | Letrec Var Exp Exp
    deriving (Eq, Show)

data E = 
    EEmpty 
    | Eapp E Exp
    | ELam Lambda E
    | ECons (Constructor E)
    | ESuml E Exp
    | ESumR Exp E
    | ECase E [CaseSamp]
    deriving (Eq, Show)

type G = Map Var Exp
data ECont = ECont E Exp G deriving (Eq, Show)
data DCont = DCont E G (Map Var Exp) deriving (Eq)
type SubstCont = Map Var Exp

instance Show DCont where
  show (DCont e g p) = "dcont : \n  e =  " ++ (show e) ++ "\n   g = " ++ show g ++ "\n   p = " ++ show p

-- ===============================
subExps :: Exp -> [Exp]
subExps e@(LVar _) =  [e]
subExps e@(Const _) = [e]
subExps e@(GVar _) = [e]
subExps e@(Cons (Constructor _ es)) = 
	Data.List.union
	([e])
	(Data.List.foldl (Data.List.union) [] (Data.List.map subExps es))
subExps le@(Lam (Lambda _ e)) = Data.List.union [le] (subExps e)
subExps ae@(App f e) = Data.List.union [ae] (Data.List.union (subExps f) (subExps e))
subExps le@(Let _ e f) = Data.List.union [le] (Data.List.union (subExps e) (subExps f))
subExps le@(Letrec _ v f) = Data.List.union [le] (Data.List.union (subExps v) (subExps f))
subExps ce@(Case e cs) = 
	Data.List.union [ce] (
		Data.List.union 
		(subExps e) 
		(Data.List.foldl (Data.List.union) [] (Data.List.map makeCaseSub cs))
	)
	where
		makeCaseSub (CaseSamp _ ej) = subExps ej
subExps se@(Sum f e) = Data.List.union [se] (Data.List.union (subExps f) (subExps e))

-- ================================

sample2Exp :: Sample -> Exp
sample2Exp (SK (Constructor v es)) = Cons (Constructor v (
    Data.List.map LVar es))
sample2Exp (SI n) = Const n

-- ============================================
makeMassiveLet :: [Var] -> [Exp] -> Exp -> Exp
makeMassiveLet [] _ e = e
makeMassiveLet (x : xs) (y : ys) e = Let x y (makeMassiveLet xs ys e) 
makeMassiveLet _ _  _ = error "ne"

makeMassiveApp :: Var -> [Var] -> Exp
makeMassiveApp g vs = Data.List.foldl (\b a -> App b (LVar a)) (GVar g) vs

makeMassiveLam :: [Var] -> Exp -> Exp
makeMassiveLam xs e = Data.List.foldr (\a b -> Lam (Lambda a b))  e xs

-- ===========================================
extendG :: G -> Var -> Exp -> G
extendG g v e = Data.Map.insert v e g
-- =============================================

freshSufIncreasor = "$"
freshSuf :: Set Var -> String
freshSuf sv = 
	let (Var v) = if (Data.Set.null sv) then (Var "x") else Data.Set.findMax sv in
        incFreshSuf "" ((length v) + 1)

incFreshSuf :: String -> Int -> String
incFreshSuf suf n  =  suf ++  (($) concat (replicate n freshSufIncreasor))

makeFreshVar :: Var -> String -> Var
makeFreshVar (Var v) suf = Var (v ++ suf)

makeFreshVarIfBv :: String -> Set Var -> Var -> Var 
makeFreshVarIfBv p bve v = 
	if (Data.Set.member v bve) then makeFreshVar v p else v 

fresh :: String -> Set Var -> Exp ->  Exp
fresh p bve (LVar v) = LVar (makeFreshVarIfBv p bve v) 
fresh _ _ e@(Const _) = e
fresh p bve (GVar v) = GVar (makeFreshVarIfBv p bve v)
fresh p bve (Cons (Constructor k es)) = 
	(Cons (Constructor k (Data.List.map (fresh p bve) es)))
fresh p bve (Lam (Lambda x ee)) = 
    let bve' = Data.Set.union bve (Data.Set.fromList [x]) in
    Lam (Lambda (makeFreshVarIfBv p bve' x) (fresh p bve' ee))
fresh p bve (App f e) = App (fresh p bve f) (fresh p bve e)
fresh p bve (Let x e f) = Let (makeFreshVarIfBv p bve x) (fresh p bve e) (fresh p bve f)
fresh p bve (Letrec x e f) = 
    let bve' = Data.Set.union bve (Data.Set.fromList [x]) in
    Letrec (makeFreshVarIfBv p bve' x) (fresh p bve' e) (fresh p bve' f)
fresh p bve (Case e cs) = Case (fresh p bve e) (Data.List.map makeCasefresh cs)
	where
		makeCasefresh arg = case arg of
			(CaseSamp (SK (Constructor k vs)) ej) -> 
				let nvs = Data.List.map (makeFreshVarIfBv p bve) vs in
				let nej = fresh p bve ej in
				(CaseSamp (SK (Constructor k nvs)) nej)
			(CaseSamp (SI n) ej) -> CaseSamp (SI n) (fresh p bve ej)
				
fresh p bve (Sum e1 e2) = Sum (fresh p bve e1) (fresh p bve e2)

mfresh :: Exp -> Set Var -> Exp 
mfresh e dvv = 
    let fofresh = Data.Set.union (allv e) dvv in
	fresh (freshSuf fofresh) (Data.Set.empty) e

freshBranchForCase :: CaseSamp -> Exp -> DCont -> CaseSamp
-- freshBranchForCase eeee@(CaseSamp px@(SK (Constructor k vs')) ex') eee (DCont r g p) =
--     let allc = allv (finilize (ECont r eee g)) in  
--     let allp = allv (sample2Exp px) in
--     let alle = allv (ex') in
--     let suf = freshSuf (Data.Set.union allc (Data.Set.union allp alle)) in
--     let ex = fresh suf allp ex' in
--     let vs = Data.List.map (\x -> makeFreshVar x suf) vs' in
--     let ret = CaseSamp (SK (Constructor k vs)) ex in
--     ret

freshBranchForCase a _ _ = a


-- ============================================


domSubst :: SubstCont -> [Var]
domSubst  subst = Data.Map.keys subst

rangeSubst :: SubstCont -> [Exp]
-- not Unique WARINING
rangeSubst subst = Data.Map.elems subst
-- =================================================


substEel:: Set Var -> Exp -> Var -> Exp -> Exp
substEel dd e@(LVar v) vo yo = if (v == vo) then mfresh yo dd else e
substEel _ e@(Const _) _ _ = e
substEel _ e@(GVar _) _ _ = e
substEel dd (Cons (Constructor k es)) vo yo = 
	Cons (Constructor k (Data.List.map (\e -> substEel dd e vo yo) es))
substEel dd (Lam (Lambda x e)) vo yo= 
	(Lam (Lambda x (substEel dd e vo yo)))
substEel dd (App f e) x y = App (substEel dd f x y) (substEel dd e x y)
substEel dd (Let x e f) v y = Let x (substEel dd e v y) (substEel dd f v y)
substEel dd (Letrec x e f) v y = Letrec x (substEel dd e v y) (substEel dd f v y)
substEel dd (Case e cs) v y = Case (substEel dd e v y) 
	(Data.List.map makeCases cs)
	where
		makeCases (CaseSamp samp ej) = CaseSamp samp (substEel dd ej v y) 
substEel dd (Sum e1 e2) v y = Sum (substEel dd e1 v y) (substEel dd e2 v y)


-- =========================================================
isSubstCompable :: SubstCont -> Exp -> Bool
isSubstCompable subst e = 
    -- False
    -- trace ("\n suka \n" ++ (show subst) ++ "\n e \n" ++ (show e))
	(if (Data.Set.null (Data.Set.intersection (bv e) 
		(Data.Set.fromList (domSubst subst)))) then
		--	True
		case (Data.List.find (\ei -> Data.Set.size (Data.Set.intersection 
			(bv e) (fv ei)) > 0) (rangeSubst subst)) of
			Just _ -> False
			Nothing -> True
	else
		False)


-- ==========================================

makeSubstCont :: [Var] -> [Exp] -> SubstCont
makeSubstCont v e = Data.Map.fromList (Data.List.zipWith (\a b -> (a, b)) v e)

applySubstCont :: Exp -> SubstCont -> Exp
applySubstCont e subst = case (Data.Map.toList subst) of
	[] -> e
	((v, x) : xs) -> applySubstCont (substEel (allv e) e v x) (Data.Map.fromList xs)


-- ====================================================
createfreshOnSplit :: DCont -> Var
createfreshOnSplit (DCont _ g p) = 
	let ks2 = Data.Map.keysSet g in
	let ks =  Data.Map.keysSet p in
	let bve = Data.Set.union ks2 ks in
	makeFreshVar (Var "x") (freshSuf bve) 



isNotFreshOnSplit :: Var -> DCont -> Bool
isNotFreshOnSplit v (DCont _ _ p) =  case (Data.Map.lookup v p) of
	Just _ -> False
	Nothing -> True

-- ============================================
isExpAnnoying :: Exp -> Bool
isExpAnnoying (LVar _) = True
--isExpAnnoying (GVar _) = True
isExpAnnoying (Sum (Const _) a) = isExpAnnoying a
isExpAnnoying (Sum a (Const _)) = isExpAnnoying a
isExpAnnoying (Sum a b) = (isExpAnnoying a) && isExpAnnoying b
isExpAnnoying (App a _) =(isExpAnnoying a)
isExpAnnoying _ = False
-- =============================================
fv :: Exp -> Set Var
fv (LVar v) = Data.Set.insert v Data.Set.empty
fv (Const _) = Data.Set.empty
fv (GVar _) = Data.Set.empty
fv (Cons (Constructor _ es)) = Data.Set.unions (Data.List.map fv es)
fv (Lam (Lambda x e)) = Data.Set.difference 	(fv e) (Data.Set.fromList [x])
fv (App f e) = Data.Set.union (fv f) (fv e)
fv (Let x e f) = Data.Set.union (fv e) (Data.Set.difference (fv f) (Data.Set.fromList [x]))
fv (Letrec _ v f) = Data.Set.union (fv v) (fv f)
fv (Case e cs) = 
	Data.Set.union 
	(fv e) 
	(Data.Set.unions (Data.List.map makeCasefv cs))
	where
		makeCasefv (CaseSamp pj ej) = 
			let fvs = fv (sample2Exp pj) in Data.Set.difference (fv ej) fvs
fv (Sum e1 e2) = Data.Set.union (fv e1) (fv e2)

-- ===================
bv :: Exp -> Set Var
bv (LVar _) = Data.Set.empty
bv (Const _) = Data.Set.empty
bv (GVar _) = Data.Set.empty
bv (Cons (Constructor _ es)) = Data.Set.unions (Data.List.map bv es)
bv (Lam (Lambda x e)) = Data.Set.union (bv e) (Data.Set.fromList [x])
bv (App f e) = Data.Set.union (bv f) (bv e)
bv (Let x e f) = Data.Set.union (bv e) (Data.Set.union (bv f) (Data.Set.fromList [x]))
bv (Letrec g v f) = Data.Set.union (bv v) (Data.Set.union (bv f) (Data.Set.fromList [g]))
bv (Case e cs) = 
	Data.Set.union 
	(bv e) 
	(Data.Set.unions (Data.List.map makeCasebv cs))
	where
		makeCasebv arg = case arg of
			(CaseSamp (SK (Constructor _ vs)) ej)->
			 	Data.Set.union 
			 	(bv ej)
			 	(Data.Set.fromList vs)
			(CaseSamp (SI _) ej) -> (bv ej)
bv (Sum e1 e2) = Data.Set.union (bv e1) (bv e2)

-- ===============================================
allv :: Exp -> Set Var
allv e = Data.Set.union (bv e) (fv e)
-- =========================
fn :: Exp -> Set Var
fn (LVar _) = Data.Set.empty
fn (Const _) = Data.Set.empty
fn (GVar g) = Data.Set.insert g Data.Set.empty
fn (Cons (Constructor _ es)) = Data.Set.unions (Data.List.map fn es)
fn (Lam (Lambda _ e)) = fn e
fn (App f e) = Data.Set.union (fn f) (fn e)
fn (Let _ e f) = Data.Set.union (fn e) (fn f)
fn (Letrec g v f) = Data.Set.difference 
	(Data.Set.union (fn v) (fn f))
    (Data.Set.fromList [g])
fn (Case e cs) = 
	Data.Set.union 
	(fn e) 
	(Data.Set.unions (Data.List.map makeCasefn cs))
	where
		makeCasefn (CaseSamp _ ej) = fn ej
fn (Sum e1 e2) = Data.Set.union (fn e1) (fn e2)

-- ========================================
makeStrictSet :: Exp -> Set Var
makeStrictSet (LVar v) = Data.Set.insert v Data.Set.empty
makeStrictSet (Const _) = Data.Set.empty
makeStrictSet (GVar _) = Data.Set.empty
makeStrictSet (Cons (Constructor _ es)) = Data.List.foldl (\ b a -> Data.Set.union b (makeStrictSet a)) Data.Set.empty es
makeStrictSet (Lam (Lambda _ _)) = Data.Set.empty
makeStrictSet (App f e) = Data.Set.union (makeStrictSet f) (makeStrictSet e)
makeStrictSet (Let x e f) = Data.Set.union (makeStrictSet e) (Data.Set.difference (makeStrictSet f) (Data.Set.fromList [x]))
makeStrictSet (Letrec _ _ f) = makeStrictSet f
makeStrictSet (Case e (cs : css)) = 
	Data.Set.union 
	(makeStrictSet e) 
	(Data.List.foldl 
		(\b a ->
			Data.Set.intersection b (makeCaseSet a))
		(makeCaseSet cs) css) 
	where
		makeCaseSet (CaseSamp pj ej) = 
			let fvs = fv (sample2Exp pj) in
			(Data.Set.difference (makeStrictSet ej) fvs)
makeStrictSet (Sum e1 e2) = Data.Set.union (makeStrictSet e1) (makeStrictSet e2)
makeStrictSet (Case e []) = makeStrictSet e


isStrict :: Var -> Exp -> Bool
isStrict v e = Data.Set.member v (makeStrictSet e)

-- ======================================
unionMaybeBool :: Maybe Bool -> Maybe Bool -> Maybe Bool
unionMaybeBool Nothing _ = Nothing
unionMaybeBool _ Nothing = Nothing
unionMaybeBool (Just e1) (Just e2) =  Just (e1 || e2)

unionsMaybeBool :: [Maybe Bool] -> Maybe Bool
unionsMaybeBool l = Data.List.foldl unionMaybeBool (Just False) l

andMaybeBool :: Maybe Bool -> Maybe Bool -> Maybe Bool
andMaybeBool Nothing _ = Nothing
andMaybeBool _ Nothing = Nothing
andMaybeBool a@(Just e1) b@(Just e2) =  if (e1 && e2) then Nothing else unionMaybeBool a b


isLinearM :: Var -> Exp -> Maybe Bool
isLinearM v1 (LVar v) = Just (v1 == v)
isLinearM _ (Const _) = Just False
isLinearM _ (GVar _) = Just False
isLinearM v (Cons (Constructor _ es)) = Data.List.foldl (unionMaybeBool) (Just False) (Data.List.map (isLinearM v) es) 
isLinearM v (Lam (Lambda x e)) = if (v == x) then Just False else isLinearM v e
isLinearM v (App f e) = unionMaybeBool (isLinearM v f) (isLinearM v e)

-- MAYBE WRONG ! 
isLinearM v (Let x e f) = if (isLinearM x f == Nothing) then Nothing else  unionMaybeBool (isLinearM v e) (isLinearM v f)
-- MAYBE WRONG ! 
isLinearM v (Letrec _ e f) = unionMaybeBool (isLinearM v e) (isLinearM v f)
-- MAYBE WRONG
isLinearM v (Case e cs) = 
	andMaybeBool
	(isLinearM v e) 
	(unionsMaybeBool (Data.List.map makeCaseLin cs))
	where
		makeCaseLin (CaseSamp pj ej) = 
			-- maybe wrong here - not unionMaybeBool need
			let lins = isLinearM v (sample2Exp pj) in unionMaybeBool lins (isLinearM v ej)
isLinearM v (Sum e1 e2) =  unionMaybeBool (isLinearM v e1) (isLinearM v e2)

isLinear ::  Var -> Exp -> Bool
isLinear v e = case (isLinearM v e) of
	(Just _) -> True
	(Nothing ) -> False

-- =====================================
takeE :: ECont -> Exp
takeE (ECont _ e _ ) = e
 -- =================================
reduceReL::ECont -> ECont
-- reduceReL econt@(ECont ee (GVar name) g) = case Data.Map.lookup name g of
--         (Just newe) -> ECont ee newe g
--         Nothing -> econt

reduceReL (ECont ee (App (Lam (Lambda x e)) v) g) = 
    let ss = makeSubstCont [x] [v] in
    ECont ee (applySubstCont e ss) g
reduceReL econt@(ECont ee (Case (Cons (Constructor k v)) cl) g) = case (Data.List.find  checkf cl) of
    (Just (CaseSamp (SK (Constructor _ xj)) ej))-> 
    	(ECont ee (applySubstCont ej (makeSubstCont xj v)) g)
    _-> econt
    where
        checkf arg = case arg of
            (CaseSamp (SK (Constructor kj _)) _) -> kj == k
            (_) -> False
reduceReL econt@(ECont ee (Case (Const n) cl) g) = case (Data.List.find 
    (\(CaseSamp (SI nj) _ )-> nj == n) cl) of
        (Just (CaseSamp (SI _) ej))-> (ECont ee ej g)
        _ -> econt
reduceReL (ECont ee (Let x v e) g) = (ECont ee (applySubstCont e (makeSubstCont [x] [v])) g)     
reduceReL (ECont ee (Sum (Const n1) (Const n2))  g) = ECont ee (Const (n1 + n2)) g

--reduceReL (ECont ee (App (Letrec x v e) e2) g) = ECont ee (Letrec x v (App e e2)) g  
--reduceReL (ECont ee (App (Letrec x v e) e2) g) = ECont ee (Letrec x (App v e2) e) g 
--reduceReL (ECont ee (App (Letrec x e@(Lam (Lambda x2 _)) (GVar _)) e2) g) = ECont ee (Letrec x e (App e e2)) g
-- reduceReL (ECont ee (App (Letrec x e@(Lam (Lambda x2 _)) e3) e2) g) = ECont ee (Letrec x e (App e3 e2)) g
-- recursive
reduceReL (ECont ee (Cons (Constructor k es)) g) = 
    let es' = Data.List.map (\a -> takeE (reduceReL (ECont ee a Data.Map.empty))) es in
    (ECont ee (Cons (Constructor k es')) g)
reduceReL (ECont ee (Lam (Lambda  x e)) g) = 
    let e' = takeE (reduceReL (ECont ee e Data.Map.empty))  in
    (ECont ee (Lam (Lambda x e')) g)
reduceReL (ECont ee (App f e) g) = 
    let e' = takeE (reduceReL (ECont ee e Data.Map.empty))  in
    let f' =  takeE (reduceReL (ECont ee f Data.Map.empty)) in
    (ECont ee (App f' e') g)
reduceReL (ECont ee (Letrec x f e) g) = 
    let e' = takeE (reduceReL (ECont ee e Data.Map.empty))  in
    let f' =  takeE (reduceReL (ECont ee f Data.Map.empty)) in
    (ECont ee (Letrec x f' e') g)
reduceReL (ECont ee (Sum f e) g) = 
    let e' = takeE (reduceReL (ECont ee e Data.Map.empty))  in
    let f' =  takeE (reduceReL (ECont ee f Data.Map.empty)) in
    (ECont ee (Sum f' e') g)
reduceReL (ECont ee (Case e cs) g) = 
    let e' = takeE (reduceReL (ECont ee e Data.Map.empty))  in
    let cs' = Data.List.map makeCaseLin cs in
    (ECont ee (Case e' cs') g)
    where
        makeCaseLin (CaseSamp pj ej) = 
            let ej' = takeE (reduceReL (ECont ee ej Data.Map.empty)) in
            (CaseSamp pj ej')


-- otherwise
reduceReL econt = econt 

-- fn (Case e cs) = 
--     Data.Set.union 
--     (fn e) 
--     (Data.Set.unions (Data.List.map makeCasefn cs))
--     where
--         makeCasefn (CaseSamp _ ej) = fn ej

reduceReLFIN :: ECont -> ECont
reduceReLFIN econt = 
	let newcont = reduceReL econt in
	if (newcont == econt) then newcont else reduceReLFIN newcont

-- ===================================================
substE :: E -> E -> E
substE (EEmpty) r = r
substE (Eapp ee1 e) ee2 = Eapp (substE ee1 ee2) e
substE (ECase ee1 arg) ee2 = ECase (substE ee1 ee2) arg
-- substE (ECaseK ee1 arg) ee2 = ECaseK (substE ee1 ee2) arg
substE (ESumR e ee1) ee2 = ESumR e (substE ee1 ee2)
substE (ESuml ee1 e) ee2 = ESuml (substE ee1 ee2) e
substE e _ =  error "SORRY"

--- =======================================
substEExp :: E -> Exp -> Exp

substEExp EEmpty e = e
substEExp (Eapp ee e2) e = App (substEExp ee e) e2
substEExp (ELam lam ee) e = App (Lam lam) (substEExp ee e)
substEExp (ECons (Constructor k ees)) e = 
	Cons (Constructor k (Data.List.map (\ee-> substEExp ee e) ees))
substEExp (ESuml ee e2) e = Sum (substEExp ee e) e2
substEExp (ESumR e1 ee) e = Sum e1 (substEExp ee e) 
substEExp (ECase ee cs) e = Case (substEExp ee e) cs



finilize :: ECont -> Exp
finilize oldcont =  
	let (ECont ee e _) = reduceReLFIN oldcont in
	takeE (reduceReLFIN (ECont EEmpty (substEExp ee e) Data.Map.empty))


-- ===========================================


drivingMassive :: [Exp] -> DCont -> [Exp]
drivingMassive es ds = Data.List.map (\e -> driving e ds) es


driving :: Exp -> DCont -> Exp
-- R1
driving n@(Const _) (DCont ee g _) =  finilize (ECont ee n g)
-- R2
driving x@(LVar _) (DCont ee g _) =  finilize (ECont ee x g)
-- R3 
driving g@(GVar _) dcont = dapp g dcont
-- R4
driving (Cons (Constructor k es)) dcont@(DCont EEmpty _ _) = (Cons (
    Constructor k (drivingMassive es dcont)))
--  don't understancd 
-- R5
driving (App (LVar x) es) (DCont r g p) = finilize (ECont r (App (LVar x) 
    (driving es (DCont EEmpty g p)) ) g)
-- dont understand
-- R6
driving (Lam (Lambda x es)) (DCont EEmpty g p) = (tracesafe "me r6\n")
    (Lam (Lambda x (driving es (DCont EEmpty g p))))
-- R7
driving (Sum (Const n1) (Const n2)) (DCont r g p) = driving 
    (finilize (ECont r (Const (n1 + n2)) g)) (DCont EEmpty g p)

-- R8
driving es@(Sum e1 e2) (DCont r g p) = 
    --if (isExpAnnoying es) then 
    -- if (True) then
    if (isExpAnnoying es) then
        let dcont = (DCont EEmpty g p) in
            Sum (driving e1 dcont) (driving e2 dcont)
    else 
        let rs = substE r (ESumR e1 EEmpty) in
        let ls =  substE r (ESuml EEmpty e2) in
        if (isExpAnnoying e1) then
            tracesafe("rs = " ++ (show rs))
            (driving e2 (DCont rs g p))
        else
            case (e1) of 
                (Const _) -> tracesafe("rs = " ++ (show rs))(driving e2 (DCont rs g p))
                (_) -> tracesafe("ls = " ++ (show ls))(driving e1 (DCont ls g p))

-- R9
driving (App (Lam (Lambda x f)) e) dcont = 
    driving (Let x e f) dcont

-- R10
driving (App e e') (DCont r g p) = 
    let re' = substE r (Eapp EEmpty e') in 
    driving e (DCont re' g p)

--R11
driving (Let x n@(Const _) f) (DCont r g p) =
    let rf = finilize (ECont r (applySubstCont f (makeSubstCont [x] [n])) g) in
    driving (rf) (DCont EEmpty g p)

-- R12 + R13
driving (Let x e f) dcont@(DCont r g p ) =  
    case e of 
        (y@(LVar yv)) -> 
            if (isNotFreshOnSplit yv dcont) then
                let rf = finilize (ECont r (applySubstCont f (makeSubstCont [x] [y])) g) in
                driving rf (DCont EEmpty g p)
            else
                expr
        _ -> expr
    where
        expr = 
            if ((isStrict x f) && (isLinear x f)) then
                let rf = finilize (ECont r (applySubstCont f (makeSubstCont [x] [e])) g) in
                driving rf (DCont EEmpty g p)
            else
                let de = driving e (DCont EEmpty g p) in
                let df = driving (finilize (ECont r f g)) (DCont EEmpty g p) in
                Let x de df


--R14 
driving (Letrec g v e) (DCont r gg p)= 
	let newg = extendG gg g v in
	let re = finilize (ECont r e newg) in
	driving re (DCont EEmpty newg p)


-- R15
driving (Case xe@(LVar x) ps') dc@(DCont r g p) = 
    -- let ps = Data.List.map (\sa -> freshBranchForCase sa xe dc) ps' in 
    let ps = ps' in 
    Case xe
    (Data.List.map (\(CaseSamp px ex) -> 
        let re = finilize (ECont r ex g) in
        let pxe = (sample2Exp px) in 
        let sre = if (not (Data.Set.member x (allv pxe))) 
            then applySubstCont re (makeSubstCont [x] [(sample2Exp px)]) 
            else re in
        let dr = driving sre (DCont EEmpty g p) in
        CaseSamp px dr
        ) ps)

-- R16
driving (Case xe@(Cons (Constructor k es)) cs') dc@(DCont r g p) = 
        -- let cs = Data.List.map (\sa -> freshBranchForCase sa xe dc) cs' in 
        let cs = cs' in
        driving (makeR(Data.List.find  (\(CaseSamp arg _ ) -> 
            case arg of
                SK (Constructor kj _) -> kj == k
                _ -> error "R16"
        ) cs)) (DCont EEmpty g p)
    where 
        makeLet :: (Maybe CaseSamp) -> Exp
        makeLet (Just (CaseSamp (SK (Constructor _ xj)) ej))  = 
            makeMassiveLet xj es ej
        makeLet _ = error "R16"

        makeR fcs = finilize (ECont r (makeLet fcs) g)
-- R17
driving (Case xe@(Const n) cs') dc@(DCont r g p) = 
        -- let cs = Data.List.map (\sa -> freshBranchForCase sa xe dc) cs' in 
        let cs = cs' in
        tracesafe ("me r17\n") (makeL (Data.List.find  (\(CaseSamp (SI nj) _) -> nj == n) cs))
    where 
        makeL :: (Maybe CaseSamp) -> Exp
        makeL (Just (CaseSamp (SI _) ej))  =
            let rj = finilize (ECont r ej g) in
            driving rj (DCont EEmpty g p)
        makeL _ = error "R17"
--R18 + R19
driving (Case e cs') dc@(DCont r g p) = 
    -- let cs = Data.List.map (\sa -> freshBranchForCase sa e dc) cs' in 
    let cs = cs' in
    if (isExpAnnoying e) then
        let da = driving (e) (DCont EEmpty g p) in
        let sampL = Data.List.map (\(CaseSamp pj ej) -> 
                let rej = driving (finilize (ECont r ej g)) (DCont EEmpty g p) in
                CaseSamp pj rej) cs in
        tracesafe ("me 18\n") (Case da sampL)
    else
        let nr = substE (r) (ECase EEmpty cs) in
        tracesafe ("me 19\n") (driving e (DCont nr g p))

-- R20
driving e (DCont r g _) = 
    finilize (ECont r e g)


-- ==========================================

homeo :: Exp -> Exp -> Bool
-- VARS
homeo (LVar _) (LVar _) = True
homeo (GVar a) (GVar b) = (a == b)

homeo (Const n) (Const m) = n == m

-- COUPLING
homeo (Cons (Constructor k es)) (Cons (Constructor k2 es')) = 
    if (not (k == k2)) then False
    else	
        case (Data.List.find (\x -> x == False) 
            (Data.List.zipWith (\e1 e2 -> (homeo e1 e2)) es es')) of
            Just _ -> False
            Nothing -> True
homeo (Lam (Lambda _ e)) (Lam (Lambda _' e')) = homeo e e'
homeo (App e1 e2) (App e1' e2') = (homeo e1 e1') && (homeo e2 e2')
homeo (Case e cs) (Case e' cs') = 
	(homeo e e') && 
	(case (Data.List.find (\x -> x == False) 
		(Data.List.zipWith (\(CaseSamp _ ee) (CaseSamp _ ee') -> (homeo ee ee')) cs cs')) of
		Just _ -> False
		Nothing -> True)
homeo (Sum e1 e2) (Sum e1' e2') = (homeo e1 e1') && (homeo e2 e2')
-- Maybe wrong
homeo (Let v e1 e2) (Let v' e1' e2') = (homeo (LVar v) (LVar v')) && (homeo e1 e1') && (homeo e2 e2')
-- Maybe wrong
homeo (Letrec v e1 e2) (Letrec v' e1' e2') = (homeo (LVar v) (LVar v')) && (homeo e1 e1') && (homeo e2 e2')

-- DIVING
homeo e (Cons (Constructor _ es')) = 
	case (Data.List.find (\e2 -> (homeo e e2)) es') of
		Just _ -> True
		Nothing -> False
homeo e (Lam (Lambda _' e')) = homeo e e'
homeo e (App e1' e2') = (homeo e e1') || (homeo e e2')
homeo e (Case e' cs') = 
	(homeo e e') || 
	(case 
		(Data.List.find (\(CaseSamp _ ee') -> (homeo e ee')) cs') of
		Just _ -> True
		Nothing -> False)
homeo e (Sum e1' e2') = (homeo e e1') || (homeo e e2')
-- -- Maybe wrong
homeo e (Let v' e1' e2') = (homeo e (LVar v')) ||  (homeo e e1') || (homeo e e2')
-- -- Maybe wrong
homeo e (Letrec v' e1' e2') = (homeo e (LVar v')) || (homeo e e1') || (homeo e e2')
homeo _ _ = False


-- ====================================
-- COMMON SUBEXPR
sc :: (Exp, SubstCont, SubstCont) -> (Exp, SubstCont, SubstCont)
sc (eeee, s1, s2) = 
    let es2 = makeme s1 s2 in
    let es1 = makeme es2 s1 in 
    if ( (Data.Map.size es2 == Data.Map.size s2) && (Data.Map.size es1 == Data.Map.size s1)) then
        pizda (eeee, (Data.Map.keys s1), s1 ,s2)
    else
        error "WTFFFF"
    
    where 
        makeme a b = 
            Data.Map.fromList
            (Data.List.filter (\(x, _) -> Data.Map.member x b) (Data.Map.toList a))

        pizda (e, [] , sa, sb) = (e, sa, sb)
        pizda (e3, (a : xs), sa, sb) = 
               let (Just e') = Data.Map.lookup a sa in
               let (Just e'') = Data.Map.lookup a sb in
               let (e, sa', sb') = (case (Data.List.find (\(k, v) ->
                    let (Just v2) = Data.Map.lookup k sb in
                    (not (k == a)) && (v == e') && (v2 == e'')) (Data.Map.toList sa)) of
                        Just (b, _) -> (
                                (applySubstCont e3 (makeSubstCont [a] [LVar b])), 
                                (Data.Map.delete a sa),
                                (Data.Map.delete a sb))
                        Nothing -> (e3, sa, sb)) in
               pizda (e, xs, sa', sb') 

-- ==============================================
-- COMMON FUNCTOR
sg :: Exp -> Exp -> String -> ( (Exp, SubstCont, SubstCont), String)
sg e1@(LVar v1) e2@(LVar v) suf = 
	if (v1 == v) then 
		( (e1, Data.Map.empty , Data.Map.empty ) , suf)
	else 
		sgcom e1 e2 suf

-- -- MAYBE WRONG
sg e1@(GVar v1) e2@(GVar v) suf = 
    if (v1 == v) then 
        ( (e1, Data.Map.empty , Data.Map.empty ) , suf)
    else 
        sgcom e1 e2 suf

sg a@(Cons (Constructor k es1)) b@(Cons (Constructor k2 es2)) suf = 
	if ((k == k2) && ((Data.List.length es1) ==  (Data.List.length es2))) then
		let ((es, s1, s2), t) = Data.List.foldl gonna (([] , Data.Map.empty , Data.Map.empty) , suf) (Data.List.zipWith (,) es1 es2)
		in
		((Cons (Constructor k es), s1, s2), t)
	else
		sgcom a b suf

    where 
        gonna  ((e, s1, s2), t)  (e1, e2) = 
            let ((e', s1', s2'), t') = sg e1 e2 t in
            ( (e ++ [e'], Data.Map.union s1 s1', Data.Map.union s2 s2'), t')

        startGonna (e1 : _ ) (e2  : _ ) = 
            let ((e, s1, s2), t) = sg e1 e2 suf 
            in  (([e], s1, s2), t)
 

-- -- Maybe wrong
sg (App e1' e2') (App e1'' e2'') suf =
	let ((e1, s1, s2), suf') = sg e1' e1'' suf in
	let ((e2, s1', s2'), suf'') = sg e2' e2'' suf' in
	( ((App e1 e2), Data.Map.union s1 s1', Data.Map.union s2 s2'), suf'')

sg (Sum e1' e2') (Sum e1'' e2'') suf =
    let ((e1, s1, s2), suf') = sg e1' e1'' suf in
    let ((e2, s1', s2'), suf'') = sg e2' e2'' suf' in
    ( ((Sum e1 e2), Data.Map.union s1 s1', Data.Map.union s2 s2'), suf'')


sg a@(Lam (Lambda v' e')) b@(Lam (Lambda v'' e'')) suf = 
	let v = makeFreshVar (Var "x") suf in
    let suf' = incFreshSuf suf 1 in
	let e'v = applySubstCont e' (makeSubstCont  [v'] [(LVar v)]) in
	let e''v = applySubstCont e'' (makeSubstCont [v''] [(LVar v)]) in 
	let ((e, s1, s2), suf'') = sg e'v e''v suf' in
	let eg = (Lam (Lambda v e)) in

	if ((isSubstCompable s1 eg) && (isSubstCompable s2 eg))
		then ((eg, s1, s2), suf'')
	else
		sgcom a b suf



sg aaa@(Case e0' cs1) bbb@(Case e0'' cs2) suf = 
    if (not (checkCompableY)) then
        sgcom aaa bbb suf
    else
	let ((e0, s0', s0''), suf') = sg e0' e0'' suf in
	let ( (cs, a1 , a2), suf'') = Data.List.foldl nextGen (([], [], []), suf') (Data.List.zipWith (,) cs1 cs2) in
    -- let  =  a in
    let eg = Case e0 cs in      
    if (doCheck a1 a2 eg) then
       
        let (s1, s2) = Data.List.foldl (\(s1'', s2'') (s1', s2') -> (Data.Map.union s1'' s1', Data.Map.union s2'' s2')) (s0', s0'')  (Data.List.zipWith (,) a1 a2) in
        ((eg, s1, s2), suf'')
    else
        sgcom aaa bbb suf
    where  
        doCheck a1 a2 eg = 
            case (Data.List.find (\ (s1, s2) -> (not (isSubstCompable s1 eg)) || (not (isSubstCompable s2 eg))) (Data.List.zipWith (,) a1 a2)) of
                Just _ -> False
                Nothing -> True

        nextGen ((el, s1, s2), suf3) ((CaseSamp (SK (Constructor k v)) e) , (CaseSamp (SK (Constructor _ v')) e')) = 
            let (s1', s2', suf', vl) = gonna v v' suf3 in
            let ( (ei, s1'', s2''), suf'') = sg (applySubstCont e  s1') (applySubstCont e' s2') suf' in
            let exp' = CaseSamp (SK (Constructor k vl)) ei in
            ( (el ++ [exp'], s1 ++ [s1''], s2 ++ [s2'']), suf'')


        -- WRONG !!!!!
        nextGen ((el, s1, s2), suf3) ((CaseSamp (SI n1) e) , (CaseSamp (SI n2) e')) = 
            -- let (s1', s2', suf', vl) = gonna v v' suf3 in
            if (not (n1 == n2)) then error "ZHESTKA"
            else
            let ( (ei, s1'', s2''), suf'') = sg e e' suf3 in
            let exp' = CaseSamp (SI n1) ei in
            ( (el ++ [exp'], s1 ++ [s1''], s2 ++ [s2'']), suf'')

        gonna a b suf'' = 
            let foldf = (\(s1, s2, suf', vl) (v1, v2)->
                    let suf2 = incFreshSuf suf' 1 in
                    let newv = makeFreshVar (Var "x") suf' in
                    (Data.Map.insert v1 (LVar newv) s1, Data.Map.insert v2 (LVar newv) s2, suf2, vl ++ [newv])) in
            Data.List.foldl foldf (Data.Map.empty, Data.Map.empty, suf'', []) (Data.List.zipWith (,) a b)

        checkCompable ((CaseSamp (SK (Constructor k v)) e) , (CaseSamp (SK (Constructor k2 v')) e2)) =
            k == k2
        checkCompable ((CaseSamp (SI n1) _) , (CaseSamp (SI n2) _)) =
            n1 == n2
        checkCompable _  = False 

        checkCompableY = case (Data.List.find (\p -> not (checkCompable p)) (Data.List.zipWith (,) cs1 cs2)) of
            Just _ -> False
            Nothing -> True


sg e1 e2 t = sgcom e1 e2 t


-- TODODODO SUM
-- ======================


sgcom :: Exp -> Exp -> String -> ( (Exp, SubstCont, SubstCont), String)
sgcom e1 e2 suf  = 
	let v = makeFreshVar (Var "x") suf in
    let suf' = incFreshSuf suf 1 in
	( ((LVar v), Data.Map.fromList ([ (v, e1) ]),  Data.Map.fromList ([ (v, e2) ])), suf')
 
-- ============================= 
msg :: Exp -> Exp -> (Exp, SubstCont, SubstCont)
msg e1 e2 = 
	-- trace ("\n e1 : \n" ++ (show e1) ++ "\n e2 : \n" ++ (show e2))
   
    let fff = Data.Set.union (allv e1) (allv e2) in 
    let (a, _) = sg e1 e2 (freshSuf fff) in
	(sc a)

-- ======================================
splitESame :: Exp -> Exp -> (Exp, [Exp], [Var])
splitESame e1 e2 = 
	let (tg, s1, _) = msg e1 e2 in
	--- MAYBE WRONG
	(tg, rangeSubst s1, domSubst s1)
-- =====================================
splitGenFrash :: String -> Int -> [Var]
splitGenFrash suf n = 
    if (n == 0) then error "FOK YOU" else
    let v' = makeFreshVar (Var "x") suf in
	Data.List.foldl(\v'' _ -> let (Var v) = (head v'') in (Var (incFreshSuf v 1)) : v'') [v'] (Data.List.replicate (n - 1) 0)


splitEDiff :: Exp -> String -> (Exp, [Exp], [Var])
splitEDiff e1@(LVar _) _ =  (e1, [], [])
splitEDiff e1@(Const _) _  = (e1, [], [])
splitEDiff e1@(GVar _) _ =  (e1, [], [])
splitEDiff e1@(Cons (Constructor k es))  suf = 
	let xs = splitGenFrash suf (length es) in
	let vs = (Data.List.map LVar xs) in
	( (Cons (Constructor k vs)), es, xs)

splitEDiff e1@(Lam (Lambda x e)) suf = 
	let v = Data.List.head (splitGenFrash suf 1) in
	( (Lam (Lambda x (LVar v))), [e], [v])

splitEDiff e1@(App f e) suf = 
	let x = (splitGenFrash suf 2) in
	let v1 = Data.List.head x in
	let v2 =  Data.List.head ( Data.List.tail x) in
	(App (LVar v1) (LVar v2), [f, e], [v1, v2])
splitEDiff e1@(Let k e f) suf = 
	let x = (splitGenFrash suf 2) in
	let v1 = Data.List.head x in
	let v2 =  Data.List.head ( Data.List.tail x) in
	(Let k (LVar v1) (LVar v2), [e, f], [v1, v2])
splitEDiff e1@(Letrec k e f) suf = 
	let x = (splitGenFrash suf 2) in
	let v1 = Data.List.head x in
	let v2 =  Data.List.head ( Data.List.tail x) in
	(Letrec k (LVar v1) (LVar v2), [e, f], [v1, v2])


splitEDiff e1@(Case e cs) suf = 
	let x = splitGenFrash suf (1 + (Data.List.length cs)) in
	let v = Data.List.head x in
	let vss = Data.List.tail x in
	let (cs', se, vs) =(Data.List.foldr (
		\(e', v') (el, se', vs') ->
			let (e'', newse, newvs) = makeCaseSub e' v' in
			(e'' : el, newse : se', newvs : vs')) ([], [], []) (Data.List.zipWith (,) cs vss)) in
	(Case (LVar v) cs', (e : se), (v : vs))
	where
		makeCaseSub (CaseSamp pj ej) v = 
			(CaseSamp pj (LVar v), ej, v)
splitEDiff e1@(Sum f e) suf = 
	let x = (splitGenFrash suf 2) in
	let v1 = Data.List.head x in
	let v2 =  Data.List.head ( Data.List.tail x) in
	(Sum (LVar v1) (LVar v2), [f, e], [v1, v2])

-- =============================
splitE :: Exp -> Exp -> (Exp, [Exp], [Var])
splitE a@(LVar _) b@(LVar _v) = splitESame a b
splitE a@(Const _) b@(Const _) = splitESame a b
splitE a@(GVar _) b@(GVar _)  = splitESame a b
splitE a@(Cons _) b@(Cons _) = splitESame a b
splitE a@(Lam _) b@(Lam _) = splitESame a b
splitE a@(App _ _) b@(App _ _) = splitESame a b
splitE a@(Let _ _ _) b@(Let _ _ _) = splitESame a b
splitE a@(Letrec _ _ _) b@(Letrec _ _ _) = splitESame a b
splitE a@(Case _ _) b@(Case _ _) = splitESame a b
splitE a@(Sum _ _) b@(Sum _ _) = splitESame a b

splitE e1 e2 = splitEDiff e1 (freshSuf (Data.Set.union (allv e1) (allv e2))) 

-- =============

uniteM ::  Maybe (Map Var Var)  ->  Maybe (Map Var Var)  ->  Maybe (Map Var Var) 
uniteM Nothing _ = Nothing
uniteM _ Nothing = Nothing
uniteM (Just a) (Just b) = 
    case (Data.List.find (\(k, v) ->
            case (Data.Map.lookup k b) of
                Just v2 -> (not (v == v2)) 
                Nothing -> False) (Data.Map.toList a)) of 
            Just _ -> Nothing
            Nothing -> Just (Data.Map.union a b)


takeo :: Var -> Var -> Set Var -> Set Var  -> Maybe (Map Var Var)
takeo v1 v2 fv1 fv2 = 
    if ((Data.Set.member v1 fv1) && (Data.Set.member v2 fv2)) then 
        Just (Data.Map.fromList [(v1, v2)])
    else 
        if ((Data.Set.notMember v1 fv1) && (Data.Set.notMember v2 fv2)) then
            Just (Data.Map.empty)
        else
            Nothing

o :: Exp -> Exp -> Set Var -> Set Var -> Maybe (Map Var Var) 
o (LVar v1) (LVar v2) fv1 fv2 = takeo v1 v2 fv1 fv2
o (Const _) (Const _) _ _ = Just (Data.Map.empty)
o (GVar g) (GVar g2) _ _  = 
    if (g == g2) then
        Just (Data.Map.empty)
    else
        Nothing

o (Cons (Constructor k e)) (Cons (Constructor k2 e2)) fv1 fv2 = 
    if (k == k2) then
        Data.List.foldl (\s (e1, e2) -> uniteM s (o e1 e2 fv1 fv2)) (Just Data.Map.empty)  (Data.List.zipWith (,) e e2)
    else
        Nothing
o a@(Lam (Lambda v1 e1)) b@(Lam (Lambda v2 e2)) fv1 fv2 = uniteM (takeo v1 v2 fv1 fv2) (o e1 e2 fv1 fv2)
o (App a b) (App a2 b2) fv1 fv2 = 
    let r1 = o a a2 fv1 fv2 in
    let r2 = o b b2 fv1 fv2 in 
    uniteM r1 r2
o (Sum a b) (Sum a2 b2) fv1 fv2 = 
    let r1 = o a a2 fv1 fv2 in
    let r2 = o b b2 fv1 fv2 in 
    uniteM r1 r2

o (Let v1 a b) (Let v2 a2 b2) fv1 fv2 = uniteM (o a a2 fv1 fv2) (uniteM (o b b2 fv1 fv2) (takeo v1 v2 fv1 fv2))
o (Letrec v1 a b) (Letrec v2 a2 b2) fv1 fv2 = uniteM (o a a2 fv1 fv2) (uniteM (o b b2 fv1 fv2) (takeo v1 v2 fv1 fv2))
o (Case e1 cs1) (Case e2 cs2) fv1 fv2 = 
    let s1 = o e1 e2 fv1 fv2 in
    let s2 = Data.List.foldl makeCaseLin (Just Data.Map.empty) (Data.List.zipWith (,) cs1 cs2) in
    uniteM s1 s2
    where
        makeCaseLin s' ((CaseSamp _ ej1), (CaseSamp _ ej2)) = uniteM s' (o ej1 ej2 fv1 fv2)
            --- in pj vars are not free
            

o _ _ _ _ = Nothing

-- splitE a@(Letrec _ _ _) b@(Letrec _ _ _) = splitESame a b
-- splitE a@(Case _ _) b@(Case _ _) = splitESame a b
-- splitE a@(Sum _ _) b@(Sum _ _) = splitESame a b


--- ============================================

-- ============
dapp :: Exp -> DCont -> Exp
dapp g@(GVar gv) dcont@(DCont r gg p)  = 

	let rg = tracesafe ("dapp") (finilize (ECont r g gg)) in
    -- if ( (Data.Map.size p) > 3) then rg else
    (tracesafe $! ("dapp top level [g, dcont, rg] = \ng = " ++ (show g) ++ "\n" ++ (show dcont) ++ "\nrg = " ++ show rg))
    (case (docntFindP dcont (\ (_, e) ->  case (o e rg (fv e) (fv rg)) of 
        Just _ -> True
        Nothing -> False)) of
        Just (h, e) -> dapp1 h e rg
        Nothing ->  
        	case (docntFindP dcont (\ (_, e) ->   (tracesafe  $! ("\n checking homeo rg \n" ++ (show rg) ++ "\n with e = \n" ++ (show e))) ((homeo rg e) && (homeo e rg)))) of 
        		Just fp -> dapp2 fp rg
        		Nothing -> 
        			case (docntFindP dcont (\ (_, e) -> (homeo e rg))) of
        				Just fp -> dapp3 fp rg
        				Nothing -> dapp4 rg)
	where
		dapp1 h e rg = let (Just subst) = o e rg (fv e) (fv rg) in
                            let fve = Data.Set.toList (fv e) in
                            let sve = Data.List.map (\k -> Data.Map.findWithDefault k k subst) fve in
                            let ret = makeMassiveApp h sve in
                            (trace $! ("\n dapp1 warn" 
                                    ++ "\n g = " ++ (show g)
                                    ++ "\n" ++ (show dcont)
                                    ++ "\n h = " ++ (show h)
                                    ++ "\n e = " ++ (show e)
                                    ++ "\n rg = " ++ (show rg)
                                    ++ "\n fve = " ++  (show fve) 
                                    ++ "\n sve = " ++ (show sve)
                                    ++ "\n ret = " ++ (show ret)
                                    ++ "\n")) 


                            (ret)


		dapp2 (h, e) rg = (trace $! ("\n dapp2 warns" 
                            ++ "\n g = " ++ (show g)
                            ++ "\n" ++ (show dcont)
                            ++ "\n rg = " ++ (show rg)
                            ++ "\n h = " ++ (show h)
                            ++ "\n e = " ++ (show e)   
                            ++ "\n"))     
                            (rg)
		
		dapp3 (h, e1) rg = 
			let (fg, f, y) = splitE rg e1 in
			let df = (drivingMassive f (DCont EEmpty gg p)) in
			let scont = makeSubstCont y df in
			let dfg = driving fg (DCont EEmpty gg p) in
			let ret = finilize (ECont EEmpty (applySubstCont dfg scont) Data.Map.empty) in
			(trace $! ("\n dapp3 warns \n" 
                            ++ "\n g = " ++ (show g)
                            ++ "\n" ++ (show dcont) 
                            ++ "\n h = " ++ (show h)
                            ++ "\n e1 = " ++ (show e1) 
                            ++ "\n rg = " ++ (show rg) 
                            ++ "\n fg = " ++ (show fg)   
                            ++ "\n f = " ++ (show f) 
                            ++ "\n y = " ++  (show y) 
                            ++ "\n df = " ++ (show df) 
                            ++ "\n scont = " ++ (show scont) 
                            ++ "\n dfg = " ++ (show dfg) 
                            ++ "\n ret = " ++ (show ret)
                            ++ "\n")
                        )(ret)

		dapp4 rg = 
			let h = createfreshOnSplit dcont in
			let p' = Data.Map.insert h rg p in
			let (Just v) = Data.Map.lookup gv gg in
			let rv = finilize (ECont r v gg) in
			let e = driving rv (DCont EEmpty gg p') in
			let x = Data.Set.toList (fv rg) in
			let sube = subExps e in

            
			(trace ("\n dapp4 warns \n"
                    ++ "\n g = " ++ (show g)
                    ++ "\n rg = " ++ (show rg)
                    ++ "\n" ++ (show dcont) 
                    ++ "\n h = " ++ (show h)
                    ++ "\n p' = " ++ (show p')
                    ++ "\n v = " ++ (show v)
                    ++ "\n rv = " ++ (show rv)
                    ++ "\n e = " ++ (show e)  
                    ++ "\n x = " ++ (show x)   
                    ++ "\n") ) (maybeTry rg e sube (if (Data.Set.member h (fn e)) then
                                    dapp4b rg h x e 
                                    else
                                    dapp4c e))



        
                maybeTry rg e sube a =  if ((Data.Map.size p)  >= 100) then
                                    case (Data.List.find (\e1 -> homeo e1 rg) sube) of
                                                Just e1 -> (dapp4a e1 rg)
                                                Nothing -> a
                                    else a


		-- Maybe wrong
		dapp4a e1 rg = (trace $! ("\n dapp4a warns \n"
                                    ++ "\n g = " ++ (show g)
                                    ++ "\n" ++ (show dcont) 
                                    ++ "\n e1 = " ++ (show e1)
                                    ++ "\n rg = " ++ (show rg)  
                                    ++ "\n")) (dapp3 ("", e1) rg)
		
		dapp4b rg h x e =
			let lxe = makeMassiveLam x e in
			let hx = makeMassiveApp h x in
			let ret = finilize (ECont EEmpty (Letrec h lxe hx) Data.Map.empty) in
			trace ("\n dapp4b warns \n"
                    ++ "\n g = " ++ (show g)
                    ++ "\n rg = " ++ (show rg)
                    ++ "\n" ++ (show dcont) 
                    ++ "\n h = " ++ (show h)
                    ++ "\n x = " ++ (show x)  
                    ++ "\n e = " ++ (show e)  
                    ++ "\n lxe = " ++ (show lxe)  
                    ++ "\n hx = " ++ (show hx)  
                    ++ "\n ret = " ++ (show ret)
                    ++ "\n") (ret)

		dapp4c e = (trace $! ("\n dapp4c warns \n"
                                ++ "\n g = " ++ (show g)
                                ++ "\n" ++ (show dcont) 
                                ++ "\n e = " ++ (show e)
                                ++ "\n")) e

		docntFindP :: DCont -> ((Var, Exp) -> Bool) -> Maybe (Var, Exp)
		docntFindP (DCont _ _ p') pred111 =
			(Data.List.find pred111 (Data.Map.toList p'))

dapp _ _ = error "dapp with no function"

