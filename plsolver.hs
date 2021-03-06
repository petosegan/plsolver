import Data.List
import qualified Data.Set as Set

data Symbol = SymbolBool Bool | SymbolString String deriving (Eq)

instance Show Symbol where
	show = renderSymbol

instance Ord Symbol where
	compare (SymbolString a) (SymbolString b) = compare a b
	compare (SymbolBool _) (SymbolString _) = GT
	compare (SymbolBool a) (SymbolBool b) = compare a b

renderSymbol :: Symbol -> String
renderSymbol (SymbolBool True) = "True"
renderSymbol (SymbolBool False) = "False"
renderSymbol (SymbolString s) = id s

data Sentence = AtomicSentence Symbol | NotSentence Sentence | AndSentence Sentence Sentence| OrSentence Sentence Sentence| ImplySentence Sentence Sentence| IffSentence Sentence Sentence deriving (Eq, Ord)

instance Show Sentence where
	show = renderSentence

renderSentence :: Sentence -> String
renderSentence (AtomicSentence sym) = show sym
renderSentence (NotSentence s1) = concat ["NOT ", renderSentence s1]
renderSentence (AndSentence s1 s2) = concat ["(", renderSentence s1, " AND ", renderSentence s2, ")"]
renderSentence (OrSentence s1 s2) = concat ["(",renderSentence s1, " OR ", renderSentence s2, ")"]
renderSentence (ImplySentence s1 s2) = concat ["(",renderSentence s1, " => ", renderSentence s2, ")"]
renderSentence (IffSentence s1 s2) = concat ["(",renderSentence s1, " <=> ", renderSentence s2, ")"]

type Model = [(Symbol, Bool)]

tt_entails :: Sentence -> Sentence -> Bool
tt_entails kb alpha = tt_check_all kb alpha symbols []
    where symbols = union (extract_symbols kb) (extract_symbols alpha)

extract_symbols :: Sentence -> [Symbol]
extract_symbols (AtomicSentence sym) = [sym]
extract_symbols (NotSentence s1) = extract_symbols s1
extract_symbols (AndSentence s1 s2) = union (extract_symbols s1) (extract_symbols s2)
extract_symbols (OrSentence s1 s2) = union (extract_symbols s1) (extract_symbols s2)
extract_symbols (ImplySentence s1 s2) = union (extract_symbols s1) (extract_symbols s2)
extract_symbols (IffSentence s1 s2) = union (extract_symbols s1) (extract_symbols s2)

tt_check_all :: Sentence -> Sentence -> [Symbol] -> Model -> Bool
tt_check_all kb alpha symbols model = if null symbols
					 then if pl_true kb model
						 then pl_true alpha model
						 else True
					 else tt_check_all kb alpha rest model_p_true && tt_check_all kb alpha rest model_p_false
					 where (p:rest) = symbols
					       model_p_true = ((p, True):model)
					       model_p_false = ((p, False):model)


pl_true :: Sentence -> Model -> Bool
pl_true (AndSentence s1 s2) model = pl_true s1 model && pl_true s2 model
pl_true (OrSentence s1 s2) model = pl_true s1 model || pl_true s2 model
pl_true (ImplySentence s1 s2) model = not (pl_true s1 model && not (pl_true s2 model))
pl_true (IffSentence s1 s2) model = (pl_true s1 model && pl_true s2 model) || (not (pl_true s1 model) && not (pl_true s2 model))
pl_true (NotSentence s1) model = not (pl_true s1 model)
pl_true (AtomicSentence s1) model = case (find (\x -> fst x == s1) model) of
						 Just value -> snd value
						 Nothing -> False

cnf_convert :: Sentence -> Sentence
cnf_convert ss = or_distribute(not_pushdown(imply_remove(iff_remove(ss))))

iff_remove :: Sentence -> Sentence
iff_remove (IffSentence s1 s2) = AndSentence (ImplySentence s1ir s2ir) (ImplySentence s2ir s1ir)
    where s1ir = iff_remove s1
	  s2ir = iff_remove s2
iff_remove (ImplySentence s1 s2) = ImplySentence (iff_remove s1) (iff_remove s2)
iff_remove (AndSentence s1 s2) = AndSentence (iff_remove s1) (iff_remove s2)
iff_remove (OrSentence s1 s2) = OrSentence (iff_remove s1) (iff_remove s2)
iff_remove (NotSentence s1) = NotSentence (iff_remove s1)
iff_remove (AtomicSentence s1) = AtomicSentence s1

imply_remove :: Sentence -> Sentence
imply_remove (ImplySentence s1 s2) = OrSentence (NotSentence (imply_remove s1)) (imply_remove s2)
imply_remove (AndSentence s1 s2) = AndSentence (imply_remove s1) (imply_remove s2)
imply_remove (OrSentence s1 s2) = OrSentence (imply_remove s1) (imply_remove s2)
imply_remove (NotSentence s1) = NotSentence (imply_remove s1)
imply_remove (AtomicSentence s1) = AtomicSentence s1

not_pushdown :: Sentence -> Sentence
not_pushdown (NotSentence (NotSentence s1)) = not_pushdown s1
not_pushdown (NotSentence (AndSentence s1 s2)) = not_pushdown (OrSentence (NotSentence s1) (NotSentence s2))
not_pushdown (NotSentence (OrSentence s1 s2)) = not_pushdown (AndSentence (NotSentence s1) (NotSentence s2))
not_pushdown (NotSentence ss) = NotSentence (not_pushdown ss)
not_pushdown (AndSentence s1 s2) = AndSentence (not_pushdown s1) (not_pushdown s2)
not_pushdown (OrSentence s1 s2) = OrSentence (not_pushdown s1) (not_pushdown s2)
not_pushdown (AtomicSentence s1) = AtomicSentence s1

or_distribute :: Sentence -> Sentence
or_distribute (OrSentence s1 (AndSentence s2 s3)) = or_distribute (AndSentence (OrSentence s1 s2) (OrSentence s1 s3))
or_distribute (OrSentence (AndSentence s1 s2) s3) = or_distribute (AndSentence (OrSentence s1 s3) (OrSentence s2 s3))
or_distribute ss@(OrSentence s1 s2) = if is_clause ss
					 then ss
					 else or_distribute (OrSentence s1_od s2_od)
					 where
					     s1_od = or_distribute s1
					     s2_od = or_distribute s2
or_distribute (AndSentence s1 s2) = AndSentence (or_distribute s1) (or_distribute s2)
or_distribute ss = ss

is_literal :: Sentence -> Bool
is_literal ss@(AtomicSentence _) = True
is_literal ss@(NotSentence (AtomicSentence _)) = True
is_literal ss = False

is_clause :: Sentence -> Bool
is_clause (OrSentence s1 s2) = (is_clause s1) && (is_clause s2)
is_clause ss = is_literal ss

is_cnf :: Sentence -> Bool
is_cnf (AndSentence s1 s2) = (is_cnf s1) && (is_cnf s2)
is_cnf ss@(OrSentence _ _) = is_clause ss
is_cnf ss = is_literal ss

type Clause = Set.Set Sentence
type CNFSentence = Set.Set Clause

cnf_form :: Sentence -> CNFSentence
cnf_form (AndSentence s1 s2) = Set.union (cnf_form s1) (cnf_form s2)
cnf_form ss = if is_clause ss
		 then Set.singleton (clausify ss)
		 else Set.empty

clausify :: Sentence -> Clause
clausify (OrSentence s1 s2) = Set.union (clausify s1) (clausify s2)
clausify ss = if is_literal ss
		   then Set.singleton ss
		   else Set.empty

clause_invert :: Clause -> Clause
clause_invert = Set.map literal_negate

literal_negate :: Sentence -> Sentence
literal_negate (NotSentence ss) = ss
literal_negate (AtomicSentence ss) = NotSentence (AtomicSentence ss)

is_tautology :: Clause -> Bool
is_tautology cc = not (Set.null (Set.intersection cc (clause_invert cc)))


pl_resolution :: Sentence -> Sentence -> Bool
pl_resolution kb alpha = pl_res_step this_cnf
    where
        this_cnf = cnf_form (cnf_convert (AndSentence kb (NotSentence alpha)))

pl_res_step :: CNFSentence -> Bool
pl_res_step clauses = if Set.member Set.empty resolvents
			   then True
			  else
			 if Set.isSubsetOf resolvents clauses
			   then False
			  else
			 pl_res_step (Set.union resolvents clauses)
		where
		    resolvents = pl_resolve clauses


clause_pairs :: CNFSentence -> Set.Set (Clause,Clause)
clause_pairs clauses = union_all (Set.map (pair_with clauses) clauses) 
    where
        pair_with clauses elt = Set.map ((,) elt) clauses
        union_all = Set.foldr Set.union Set.empty

pl_resolve :: CNFSentence -> Set.Set Clause
pl_resolve clauses = Set.filter (not . is_tautology) (Set.map pl_resolve_single c_pairs)
    where
        c_pairs = clause_pairs clauses

pl_resolve_single :: (Clause, Clause) -> Clause
pl_resolve_single (c1, c2) =  if Set.null $ Set.intersection c1 (clause_invert c2)
				 then taut_clause
				 else if (Set.size (Set.intersection c1 (clause_invert c2)) >= 2)
				 then taut_clause
				 else Set.union (Set.difference c1 (Set.intersection c1 (clause_invert c2))) (Set.difference c2 (Set.intersection c2 (clause_invert c1)))

dummy_sentence = AtomicSentence (SymbolString "Dummy")
taut_clause = Set.fromList [dummy_sentence, (NotSentence dummy_sentence)]


p11 = SymbolString "P11"
p12 = SymbolString "P12"
p21 = SymbolString "P21"
p22 = SymbolString "P22"
p31 = SymbolString "P31"

b11 = SymbolString "B11"
b21 = SymbolString "B21"

p11s = AtomicSentence p11
p12s = AtomicSentence p12
p21s = AtomicSentence p21
p22s = AtomicSentence p22
p31s = AtomicSentence p31

b11s = AtomicSentence b11
b21s = AtomicSentence b21

r1 = NotSentence p11s
r2 = IffSentence b11s (OrSentence p12s p21s)
r3 = IffSentence b21s (OrSentence p11s (OrSentence p22s p31s))

r4 = NotSentence b11s
r5 = b21s

kb = AndSentence r1 (AndSentence r2 (AndSentence r3 (AndSentence r4 r5)))

ortest = AndSentence (OrSentence (AndSentence p11s b11s) (AndSentence p12s b21s)) p22s
ortest2 = OrSentence ortest ortest

clausetest = (OrSentence (OrSentence p11s p12s) p31s)
clausetest2 = (OrSentence (AndSentence p11s p12s) (OrSentence p11s p12s))

kb_cnf = cnf_form (cnf_convert kb)

alpha = r1

cnftest = cnf_form (cnf_convert (AndSentence kb (NotSentence alpha)))

kb_debug = cnf_form (cnf_convert r2)
