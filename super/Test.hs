{-# OPTIONS_GHC -fno-warn-tabs #-}
{-# LANGUAGE BangPatterns #-}
import Super
import Data.Map
import Data.Set
import Data.List
import Control.DeepSeq
import Data.List.Utils

iden :: Int -> String
iden i = ($) concat (replicate i " ")

ide :: Int -> String -> String
ide i s = 
  let (s', b) = if (startswith "\n" s) then ((drop 1 s), "\n") else (s, "") in 
  b ++(iden i) ++ (replace "\n" ("\n" ++ (iden i)) s')
  
ident = 2


pretty' :: Int -> Exp -> String
pretty' i e = (iden i) ++ (pretty'' i e)

pretty'' :: Int -> Exp -> String
pretty'' _ (LVar (Var v)) = v
pretty'' _ (Const n) = (show n)
pretty'' _ (GVar (Var g)) = g
pretty'' i (Cons (Constructor k es)) = "( new " ++ k ++ " from \n" 
  ++ (Data.List.foldl (\b a -> b ++ (ide (i + ident) "\n|| ") ++ a ++ "\n") "" 
    (Data.List.map (\ e -> pretty'' (i + ident) e) es)) 
  ++ (ide i "\n)\n")
pretty'' i (Lam (Lambda (Var x) e)) = "(\\ " ++ x ++ " -> \n" 
  ++ (pretty' (i+ident) e) ++ (ide i "\n)\n")
pretty'' i (App f e) = "(" ++  
  (pretty'' (i + ident) f)  ++ ") (" ++ (pretty'' (i+ident) e) ++ ")"
pretty'' i (Let x e f) = 
  "( Let " ++ (show x) ++ " =  \n" 
  ++ (pretty' (i + ident) e) ++ (ide i "\n) in (") ++ "\n" ++ (pretty' (i + ident) f) ++ (ide i "\n)")
pretty'' i (Letrec x e f) = 
  "( Letrec " ++ (show x) ++ " =  \n" 
  ++ (pretty' (i + ident) e) ++ (ide i "\n) in (") ++ "\n" ++ (pretty' (i + ident) f) ++ (ide i "\n)")
pretty'' i (Case e cs) = "( Case " ++ (pretty'' (i+ident) e) ++ ( " of \n") ++ 
    (Data.List.foldl (++) "" (Data.List.map makeCasefn cs)) ++ (ide i "\n)")
    where
        makeCasefn (CaseSamp (SK (Constructor k v)) ej) =   
          (ide (i+ident) "{(") ++ (show k) ++ " " ++ (show v) ++ ") -> \n" 
          ++ (pretty' (i+ident*2) ej) ++ (ide (i+ident)"\n}") ++ "\n"
        makeCasefn (CaseSamp (SI n) ej) = 
          (ide (i+ident) "{(") ++ (show n) ++  ") -> \n" 
          ++ (pretty' (i+ident*2) ej) ++ (ide (i+ident) "\n}") ++ "\n"
pretty'' i (Sum e f) = (pretty'' (i + ident) e) ++ (" + ") ++ (pretty'' (i+ident) f)

removeEmpty :: String -> String
removeEmpty s = 
  let s' = replace "\n\n" "\n" s in
  let a' = Data.List.Utils.split "\n" s' in
  let ret = (Data.List.foldl (\b a -> case (Data.List.find (\x -> not (x == ' ')) a) of
        Just _ -> b ++ "\n" ++ a
        Nothing -> b) "" a') in 
  ret ++ "\n"


pretty e = (removeEmpty (pretty' 0 e))

-- ====================================


varSimplerMaybeSubst :: Var -> Set Var -> Set Var -> Var

 
varSimplerMaybeSubst v cant all  =  
  if (Data.Set.notMember v cant) then
    let (Just i) = Data.Set.lookupIndex v all in
    Var ("_x" ++ (show i))
  else
    v

varSimpler :: Exp -> Set Var -> Set Var -> Exp
varSimpler (LVar v) cant all  = LVar  (varSimplerMaybeSubst v cant all)
varSimpler e@(Const _) _ _  = e
varSimpler (GVar v) cant all = GVar (varSimplerMaybeSubst v cant all)
varSimpler (Cons (Constructor k es')) cant all = 
  let es = Data.List.map (\e -> varSimpler e cant all) es' in
  (Cons (Constructor k es))
varSimpler (Lam (Lambda v' e')) cant all = 
  let v = varSimplerMaybeSubst v' cant all in
  let e = varSimpler e' cant all in
  (Lam (Lambda v e))
varSimpler (App f e) cant all =  App (varSimpler f cant all) (varSimpler e cant all)
varSimpler (Let v' e' f') cant all = 
  let v = varSimplerMaybeSubst v' cant all in
  let e = varSimpler e' cant all in
  let f = varSimpler f' cant all in
  (Let v e f)
varSimpler (Letrec v' e' f') cant all = 
  let v = varSimplerMaybeSubst v' cant all in
  let e = varSimpler e' cant all in
  let f = varSimpler f' cant all in
  (Letrec v e f)

varSimpler (Case e' cs') cant all = 
  let e = varSimpler e' cant all in
  let cs = Data.List.map go cs' in
  Case e cs 
  where
    go (CaseSamp (SK (Constructor k vs')) ej') = 
      let vs = Data.List.map (\v -> varSimplerMaybeSubst v cant all) vs' in
      let ej = varSimpler ej' cant all in
      (CaseSamp (SK (Constructor k vs)) ej)
    go (CaseSamp s@(SI _) ej') = 
      let ej = varSimpler ej' cant all in
      (CaseSamp s ej)
varSimpler (Sum f e) cant all = Sum (varSimpler f cant all) (varSimpler e cant all)

-- =========================================

 

appendE = Lam (Lambda (Var "xsssss") (Lam (Lambda (Var "ysssss") (Case (LVar (Var "xsssss")) 
	[ 
	  (CaseSamp (SK (Constructor "list_nil" [])) (LVar (Var "ysssss"))),

	  (CaseSamp (SK (Constructor "list_app" [(Var "x'"), (Var "xs''")]))
	  		(Cons (Constructor "list_app" [(LVar (Var "x'")), 
	  			(App (App (GVar (Var "append")) (LVar (Var "xs''"))) (LVar (Var "ysssss")))])))
	]))))

iterateE = Lam (Lambda (Var "f") (Lam (Lambda (Var "a")
            (Cons (Constructor "list_app" [(LVar (Var "a")),  
                (App (App (GVar (Var "iterate")) (LVar (Var "f"))) (App (LVar (Var "f")) (LVar (Var "a"))))])))))

mapE :: Exp
mapE =  (Lam (Lambda (Var "f") (Lam (Lambda (Var "xs") (

 Case (LVar (Var "xs")) 
 [ 
   (CaseSamp (SK (Constructor "list_nil" [])) (Cons (Constructor "list_nil" []))) ,

   (CaseSamp (SK (Constructor "list_app" [(Var "x"), (Var "xs'")]))
         (Cons (Constructor "list_app" [App (LVar (Var "f")) (LVar (Var "x")), 
             (App (App (GVar (Var "map")) (LVar (Var "f"))) (LVar (Var "xs'")))])))
 ])))))

sumE :: Exp
sumE =  (Lam (Lambda (Var "xs") (
 Case (LVar (Var "xs")) 
 [ 
   (CaseSamp (SK (Constructor "list_nil" [])) (Const 0)),

   (CaseSamp (SK (Constructor "list_app" [(Var "x"), (Var "xs'")]))
         (Sum (LVar (Var "x"))
             (App (GVar (Var "sum")) (LVar (Var "xs'")))))
 ])))

eqE :: Exp
eqE = Lam (Lambda (Var "xs") (
    Case (LVar (Var "xs")) 
    [
        (CaseSamp (SI 1) (Const 5)),
        (CaseSamp (SI 0) (Const 2))
    ]))


concatE =  (Lam (Lambda (Var "zs") (
 Case (LVar (Var "zs")) 
 [ 
   (CaseSamp (SK (Constructor "list_nil" [])) (Cons (Constructor "list_nil" []))),

   (CaseSamp (SK (Constructor "list_app" [(Var "a"), (Var "b")]))
         (App (App (GVar (Var "append")) (LVar (Var "a"))) (App (GVar (Var "concat")) (LVar (Var "b")))))
 ])))

lengthE =  (Lam (Lambda (Var "huy") (
 Case (LVar (Var "huy")) 
 [ 
   (CaseSamp (SK (Constructor "list_nil" [])) (Const 0)),

   (CaseSamp (SK (Constructor "list_app" [(Var "x"), (Var "xssss")]))
         (Sum (Const 1) (App (GVar (Var "length")) (LVar (Var "xssss")))))
 ])))

filterE =  (Lam (Lambda (Var "p") (Lam (Lambda (Var "l") ( 
 Case (LVar (Var "l")) 
 [ 
   (CaseSamp (SK (Constructor "list_nil" [])) (Cons (Constructor "list_nil" []))),
   (CaseSamp (SK (Constructor "list_app" [(Var "x"), (Var "xs")]))
        (Case (App (LVar (Var "p")) (LVar (Var "x")))
        [ (CaseSamp (SI 0)
          (App (App (GVar (Var "filter")) (LVar (Var "p"))) (LVar (Var "xs")))),
          (CaseSamp (SI 1) 
          (Cons (Constructor "list_app" [
              (LVar (Var "x")),
              (App (App (GVar (Var "filter")) (LVar (Var "p"))) (LVar (Var "xs")))
            ])))  
        ])
    )
 ])))))

composeE =  (Lam (Lambda (Var "p") (Lam (Lambda (Var "f") (Lam (Lambda (Var "ys")
   (App (LVar (Var "p")) (App (LVar (Var "f")) (LVar (Var "ys"))))))))))

emptyE =  (Lam (Lambda (Var "zs") (
 Case (LVar (Var "zs")) 
 [ 
   (CaseSamp (SK (Constructor "list_nil" [])) (Const 1)),

   (CaseSamp (SK (Constructor "list_app" [(Var "x"), (Var "xs")])) (Const 0))
 ])))

-- ====================================== 

testSymbols = (Data.Map.fromList [((Var "map"), mapE), 
        ((Var "sum"), sumE),
         ((Var "eq"), eqE),
          ((Var "concat"), concatE),
          ((Var "append"), appendE),
          ((Var "iterate"), iterateE),
          ((Var "length"), lengthE),
          ((Var "empty"), emptyE),
          ((Var "filter"), filterE),
          ((Var "compose"), composeE)
          ])


testStart = DCont 
    EEmpty 
    testSymbols
    Data.Map.empty

-- ================================ 

test1 = (App (App (GVar (Var "map")) (LVar (Var "f2"))) (LVar (Var "xs")))
test2 = (App (App (GVar (Var "append")) (LVar (Var "xs"))) (LVar (Var "ys")))
test3 = (App (GVar (Var "sum")) (App (App (GVar (Var "map")) (LVar (Var "square_undefined"))) (LVar (Var "ys"))))
test4 = (App (GVar (Var "length")) (App (GVar (Var "concat")) (LVar (Var "xs"))))
test5 = (App (GVar (Var "sum")) (App (App (GVar (Var "map")) (GVar (Var "length"))) (LVar (Var "xs"))))

test6 = (App (App (GVar (Var "append"))
  (App (App (GVar (Var "map")) (LVar (Var "f"))) (LVar (Var "xs"))))
  (App (App (GVar (Var "map")) (LVar (Var "f"))) (LVar (Var "ys"))))


test7 = (App 
  (App (GVar (Var "map")) (LVar (Var "f")))
   (App (App (GVar (Var "append")) (LVar (Var "xs"))) (LVar (Var "ys"))))

test8 = (App (App (GVar (Var "filter"))
  (LVar (Var "p")))
  (App (App (GVar (Var "map")) (LVar (Var "f"))) (LVar (Var "xs"))))

test9 = (App (App (GVar (Var "map"))
  (LVar (Var "ff")))
  (App (App (GVar (Var "filter"))
    (App (App (GVar (Var "compose")) (LVar (Var "ppppp"))) (LVar (Var "ff"))))
    (LVar (Var "xsxxx"))))

test10 = (App (App (GVar (Var "map")) (LVar (Var "f"))) (App (GVar (Var "concat")) (LVar (Var "xs"))))

test11 = (App (GVar (Var "concat")) 
  (App (App (GVar (Var "map")) (App (GVar (Var "map")) (LVar (Var "f"))))
    (LVar (Var "xs"))))

test12 = (App (App (GVar (Var "iterate")) (LVar (Var "f"))) (App (LVar (Var "f")) (LVar (Var "x"))))
test13 = (App (App (GVar (Var "map")) (LVar (Var "f"))) (App (App (GVar (Var "iterate")) (LVar (Var "f"))) (LVar (Var "x"))))




testE = (App (App (GVar (Var "filter"))
    (App (App (GVar (Var "compose")) (LVar (Var "p"))) (LVar (Var "f"))))
    (LVar (Var "xs")))

testList = [test1, test2, test3, test4, test5, test6, test7, test8, test9, test10, test11, test12,
  test13]
--- ==============
runTest :: Exp -> (Exp, Exp)
runTest src = 
  let e = driving src testStart in
  let cant = (Data.Set.union (fv e) (Data.Map.keysSet testSymbols)) in
  let e2 = varSimpler e cant (allv e) in 
  (e, e2)

pretty1 (e, _) = pretty e
pretty2 (_, e) = pretty e


-- =======================

doall :: [IO ()] -> IO ()
doall [] = return ()
doall (x:xs) = do 
  x 
  (doall xs)
  

printE :: Exp -> IO ()
printE e =  putStrLn (pretty e)

printME :: [(Var, Exp)] -> IO ()
printME m = do
  doall (Data.List.map (\((Var a), b) -> do
    putStrLn a
    putStrLn (pretty b)) m)

printLE :: [Exp] -> IO ()
printLE m = do
  doall (Data.List.map (\b -> do
    putStrLn "\n"
    putStrLn (pretty b)) m)


printSymbols :: IO ()
printSymbols = do
    putStrLn "\nSymbols : " 
    putStrLn (($) concat (replicate 30 "=")) 
    doall (Data.List.map (\((Var a), b) -> do
      putStrLn ("\n" ++ a ++ ":" )
      putStrLn $ pretty b
      putStrLn (($) concat (replicate 20 "-"))
      ) (Data.Map.toList testSymbols))
    putStrLn (($) concat (replicate 30 "=")) 

printTests withOrig = do
    putStrLn "\n Test block begins : " 
    putStrLn (($) concat (replicate 30 "="))
    doall (Data.List.map (\ test -> do
          putStrLn "\n RUN TEST"
          putStrLn (($) concat (replicate 20 "*"))
          putStrLn $ pretty test
          let res = runTest test 
          putStrLn (($) concat (replicate 20 "-"))
          putStrLn "\n RESULT : "
          putStrLn $ pretty2 res
          putStrLn (($) concat (replicate 20 "-"))
          if (withOrig > 0) then do
            putStrLn "\n ORIG RESULT : "
            putStrLn $ pretty1 res
            putStrLn (($) concat (replicate 20 "-"))
          else
            return ()
          if (withOrig > 1) then  do
            putStrLn "\n WITHOUT PRETTY RESULT : "
            putStrLn $ (show res)
            putStrLn (($) concat (replicate 20 "-"))
          else 
            return ()
      ) testList)

runTestSuite :: Int -> IO () 
runTestSuite withOrig = do
  printSymbols
  printTests withOrig