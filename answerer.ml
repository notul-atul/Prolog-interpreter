exception NotUnif ;;
exception Exhausted ;;
exception AnswerFound ;;

let defineSubstitutionUHE varmap = 
	let rec uheHelper var = match var with
	| VARTERM ( v ) -> if Hashtbl.mem varmap ( VARTERM( v ) ) then Hashtbl.find varmap ( VARTERM( v ) ) else
		VARTERM( v )
	|	PREDTERM( p ) -> PREDTERM( p )
	| NUMTERM( n ) -> NUMTERM( n )
	| ATOMTERM( ATOM( p, tl ) ) -> ATOMTERM( ATOM( p, List.map uheHelper tl ) )
	in
	uheHelper
;;

let id = defineSubstitutionUHE ( Hashtbl.create 1 ) ;;

let composeSubstitutn sigma1 sigma2 =
	let compositionHelper var = sigma2( sigma1 var ) in
	compositionHelper
;;

let rec mgu term1 term2 =
	let rec searchVARTERM termlist vart = match termlist with
	| [] -> false
	| ( VARTERM( v ) )::bd -> if vart = ( VARTERM( v ) ) then true else 
		searchVARTERM bd vart
	|	( PREDTERM( p ) )::bd -> searchVARTERM bd vart
	| ( NUMTERM( n ) )::bd -> searchVARTERM bd vart
	| ( ATOMTERM( ATOM( p, tl ) ) )::bd -> if ( searchVARTERM tl vart ) then true else
		searchVARTERM bd vart
	in
	
	let substutedMGU substn t1 t2 = composeSubstitutn substn ( mgu (substn t1) (substn t2) ) in
	
	match ( term1, term2 ) with
	| ( VARTERM( v1 ), VARTERM( v2 ) ) -> if v1 = v2 then id else
		let vmap = Hashtbl.create 1 in
		let unused = Hashtbl.add vmap term1 term2 in
		defineSubstitutionUHE vmap
	|	( VARTERM( v ), PREDTERM( p ) ) -> 
		let vmap = Hashtbl.create 1 in
		let unused = Hashtbl.add vmap term1 term2 in
		defineSubstitutionUHE vmap
	|	( VARTERM( v ), NUMTERM( n ) ) -> 
		let vmap = Hashtbl.create 1 in
		let unused = Hashtbl.add vmap term1 term2 in
		defineSubstitutionUHE vmap
	|	( VARTERM( v ), ATOMTERM( ATOM(p, tl ) ) ) -> if ( searchVARTERM tl term1 ) then raise NotUnif else
		let vmap = Hashtbl.create 1 in
		let unused = Hashtbl.add vmap term1 term2 in
		defineSubstitutionUHE vmap
	|	( PREDTERM( p1 ), PREDTERM( p2 ) ) -> if p1 = p2 then id else
		raise NotUnif
	| ( NUMTERM( n1 ), NUMTERM( n2 ) ) -> if n1 = n2 then id else
		raise NotUnif
	|	( PREDTERM( p ), ATOMTERM( _ ) ) -> raise NotUnif
	| ( NUMTERM( n ), ATOMTERM( _ ) ) -> raise NotUnif
	| ( NUMTERM( n ), PREDTERM( p ) ) -> raise NotUnif
	| ( ATOMTERM( ATOM( p1, tl1 ) ), ATOMTERM( ATOM( p2, tl2 ) ) ) -> if ( ( p1 <> p2 ) || ( ( List.length tl1 ) <> ( List.length tl2 ) ) ) then
		raise NotUnif else
		List.fold_left2 (substutedMGU) (id) tl1 tl2
	|	( t1, t2 ) -> mgu t2 t1
;;

(* ******************************************************************************************************************************************* *)
let substitutionStack = ref [] ;;
let namingStack = ref [] ;;
let queryStack = ref [] ;;
let possibilitiesStack = ref [] ;;

let renameVars sigma body =
	let newNamingRule = Hashtbl.create 10 in
	
	let rec termListRenamer termlist = match termlist with
	| [] -> []
	| ( VARTERM( Var( v ) ) )::bd ->
		let newVar = sigma ( VARTERM( Var( v ) ) ) in
		let unused = if Hashtbl.mem newNamingRule newVar  then () else 
			match newVar with
			| VARTERM( Var( v2 ) ) -> Hashtbl.replace newNamingRule newVar ( VARTERM( Var( v2^( "$" ) ) ) )
		in
		newVar::( termListRenamer bd )
	| ( NUMTERM( n ) )::bd -> ( NUMTERM( n ) )::( termListRenamer bd )
	| ( PREDTERM( p ) )::bd -> ( PREDTERM( p ) )::( termListRenamer bd )
	| ( ATOMTERM( ATOM( p, tl ) ) )::bd -> 
		let newtl = termListRenamer tl in
		( ATOMTERM( ATOM( p, newtl ) ) )::( termListRenamer bd )
	in
	
	let getNewVar oldVar = 
		let newVar = sigma oldVar in
		let unused = if Hashtbl.mem newNamingRule newVar  then () else 
			match newVar with
			| VARTERM( Var( v2 ) ) -> Hashtbl.replace newNamingRule newVar ( VARTERM( Var( v2^( "$" ) ) ) )
		in
		newVar
	in
	
	let rec renamerHelper bdy = 
		match bdy with
		| [] ->
			let newSigma = defineSubstitutionUHE newNamingRule in
			let unused = namingStack := ( composeSubstitutn sigma newSigma ) :: !namingStack in 
			[]
		| NTS::bd -> NTS::( renamerHelper bd )
		| ATOMCOMP( ATOM( p, tl ) ):: bd -> 
			let newTermlist = termListRenamer tl in
			ATOMCOMP( ATOM( p, newTermlist ) )::( renamerHelper bd )
		| EQCHECKCOMP( EQCHECK( v1, v2 ) )::bd -> 
			let newVar1 = match v1 with
			| VARTERM( x1 ) -> getNewVar ( VARTERM( x1 ) )
			| y1 -> y1
			in
			let newVar2 = match v2 with
			| VARTERM( x2 ) -> getNewVar ( VARTERM( x2 ) )
			| y2 -> y2
			in
			EQCHECKCOMP( EQCHECK( newVar1, newVar2 ) )::( renamerHelper bd)
		| SUBASSGNCOMP( SUBASSGN( v1, v2, v3 ) )::bd ->
			let newVar1 = match v1 with
			| VARTERM( x1 ) -> getNewVar ( VARTERM( x1 ) )
			| y1 -> y1
			in
			let newVar2 = match v2 with
			| VARTERM( x2 ) -> getNewVar ( VARTERM( x2 ) )
			| y2 -> y2
			in
			let newVar3 = match v3 with
			| VARTERM( x3 ) -> getNewVar ( VARTERM( x3 ) )
			| y3 -> y3
			in
			SUBASSGNCOMP( SUBASSGN( newVar1, newVar2, newVar3 ) )::( renamerHelper bd)
	in
	renamerHelper body
;;

let applySubstitutionOnComponent sigma component =
	let rec subsOntermlist termlist = match termlist with
	| [] -> []
	| ( VARTERM( v ) )::bd -> ( sigma ( VARTERM( v ) ) )::( subsOntermlist bd )
	| ( PREDTERM( p ) )::bd -> ( PREDTERM( p ) )::( subsOntermlist bd )
	| ( NUMTERM( n ) )::bd -> ( NUMTERM( n ) )::( subsOntermlist bd )
	| ( ATOMTERM( ATOM( p, tl ) ) )::bd ->
		let newTermlist = subsOntermlist tl in
		( ATOMTERM( ATOM( p, newTermlist ) ) )::( subsOntermlist bd )
	in
		
	match component with
	| NTS -> NTS
	| ATOMCOMP( ATOM( p, tl ) ) -> ATOMCOMP( ATOM( p, subsOntermlist tl ) )
	| EQCHECKCOMP( EQCHECK( v1, v2 ) ) -> EQCHECKCOMP( EQCHECK( sigma v1, sigma v2 ) )
	| SUBASSGNCOMP( SUBASSGN( v1, v2, v3 ) ) -> SUBASSGNCOMP( SUBASSGN( sigma v1, sigma v2, sigma v3 ) )
;;

let variables component = 
	let check = Hashtbl.create 25 in
	
	let rec varsInTermlist termlist = match termlist with
	| [] -> []
	| VARTERM( v )::bd -> if Hashtbl.mem check v then ( varsInTermlist bd ) else
		let unused = Hashtbl.add check v true in
		VARTERM( v )::( varsInTermlist bd )
	|	PREDTERM( p )::bd -> ( varsInTermlist bd )
	| NUMTERM( n )::bd -> ( varsInTermlist bd )
	| ATOMTERM( ATOM( p, tl ) )::bd -> (varsInTermlist tl )@( varsInTermlist bd )
	in
	
	match component with
	| ATOMCOMP( ATOM( p, tl ) ) -> varsInTermlist tl
	| _ -> []
;;

let rec answerTracker () = 
	
	let query = 
		try
			if( List.length !queryStack = 0 ) then raise Not_found else List.hd ( ( List.hd !queryStack ) )
		with Failure "hd" -> raise AnswerFound
	in
	
	match query with
	|	ATOMCOMP( ATOM( p, tl ) ) ->
		let possibilities = ref ( if (List.length !queryStack <> List.length !possibilitiesStack) then Hashtbl.find database p else ( List.hd !possibilitiesStack ) ) in
		
		let rec mguFinder query = match (query, !possibilities) with
		|	( ATOMCOMP( ATOM( p1, tl1 ) ), [] ) ->
			let unused = possibilitiesStack := if (List.length !queryStack <> List.length !possibilitiesStack) then !possibilitiesStack else List.tl !possibilitiesStack in
			let unused = substitutionStack := List.tl !substitutionStack in
			let unused = namingStack := List.tl !namingStack in
			let unused = queryStack := List.tl !queryStack in
			raise Exhausted
		| ( ATOMCOMP( ATOM( p1, tl1 ) ),  ( ATOMCOMP( ATOM( p2, tl2 ) )::bd1 )::bd2 ) ->
			let first = ATOMCOMP( ATOM( p2, tl2 ) )::bd1 in
			let first = renameVars (List.hd !namingStack) first in
			let unused = possibilities := first::( List.tl !possibilities ) in
			let head = match first with
			|  ATOMCOMP( ATOM( pt, tlt ) )::bdt -> ATOMTERM( ATOM( pt, tlt ) )
			in
			try
				mgu ( ATOMTERM( ATOM( p1, tl1 ) ) ) head
			with NotUnif -> 
				let unused = namingStack := List.tl !namingStack in
				let unused = possibilities := bd2 in
				mguFinder query
		in
		
		let unifier =  composeSubstitutn ( (List.hd !substitutionStack) ) ( mguFinder query ) in
		let unused = possibilitiesStack := if (List.length !queryStack <> List.length !possibilitiesStack) then ( List.tl !possibilities )::!possibilitiesStack else
			( List.tl !possibilities )::( List.tl !possibilitiesStack )
		in
		let goal = List.tl ( List.hd !queryStack ) in
		let first = List.hd !possibilities in
		let first = List.tl first in
		let first = if List.length first = 0 then [] else ( applySubstitutionOnComponent unifier ( List.hd first ) )::( List.tl first ) in
		let unused = substitutionStack := unifier::!substitutionStack in
		let goal = if List.length first = 0 then if List.length goal =0 then [] else
			( applySubstitutionOnComponent unifier ( List.hd goal ) )::( List.tl goal ) else goal in
		let unused = queryStack := ( first@ goal )::!queryStack in
		(
		 try
			 answerTracker ()
		 with Exhausted -> answerTracker()
		)
		
	|	NTS ->
		let shadowCopyQueryStack = !queryStack in
		let shadowCopyPossibilitiesStack = !possibilitiesStack in
		let shadowCopyNamingStack = !namingStack in
		let shadowCopySubstitutionStack = !substitutionStack in
		let unused = possibilitiesStack :=  []::!possibilitiesStack in
		let freshQuery = List.hd ( List.tl ( List.hd !queryStack ) ) in
		let freshQuery = applySubstitutionOnComponent ( List.hd !substitutionStack ) freshQuery in
		let unused = queryStack := [freshQuery]::!queryStack in

		if ( ( variables freshQuery ) <> [] ) then
			let shadowCopyQueryStack = List.tl shadowCopyQueryStack in
			let shadowCopyNamingStack = List.tl shadowCopyNamingStack in
			let shadowCopySubstitutionStack = List.tl shadowCopySubstitutionStack in
			let unused = queryStack := shadowCopyQueryStack in
			let unused = namingStack := shadowCopyNamingStack in
			let unused = substitutionStack := shadowCopySubstitutionStack in
			let unused = possibilitiesStack := shadowCopyPossibilitiesStack in
			raise Exhausted
		
		else 		
		(
			try
				answerTracker ()
			with
			| AnswerFound -> 
				let shadowCopyQueryStack = List.tl shadowCopyQueryStack in
				let shadowCopyNamingStack = List.tl shadowCopyNamingStack in
				let shadowCopySubstitutionStack = List.tl shadowCopySubstitutionStack in
				let unused = queryStack := shadowCopyQueryStack in
				let unused = namingStack := shadowCopyNamingStack in
				let unused = substitutionStack := shadowCopySubstitutionStack in
				let unused = possibilitiesStack := shadowCopyPossibilitiesStack in
				raise Exhausted
			| Exhausted -> 
				let unused = queryStack := shadowCopyQueryStack in
				let unused = namingStack := shadowCopyNamingStack in
				let unused = substitutionStack := shadowCopySubstitutionStack in
				let unused = possibilitiesStack := shadowCopyPossibilitiesStack in
				let nextQuery = List.tl ( List.tl ( List.hd !queryStack ) ) in
				let unused = queryStack := nextQuery::( List.tl !queryStack ) in
				answerTracker() 
		)

	|	EQCHECKCOMP( EQCHECK( v1, v2 ) ) -> if ( List.hd !possibilitiesStack = [] && List.length !queryStack = List.length !possibilitiesStack )
		then
			let unused = possibilitiesStack :=  List.tl !possibilitiesStack in
			let unused = substitutionStack := List.tl !substitutionStack in
			let unused = namingStack := List.tl !namingStack in
			let unused = queryStack := List.tl !queryStack in
			raise Exhausted
		else
			if v1 = v2 then
				let unifier = List.hd !substitutionStack in
				let unused = substitutionStack := unifier::!substitutionStack in
				let unused = namingStack := ( List.hd !namingStack )::!namingStack in
				let first = List.tl ( List.hd !queryStack ) in
				let first = if ( List.length first = 0 ) then [] else ( applySubstitutionOnComponent unifier ( List.hd first ) )::List.tl first in
				let unused = queryStack := first::( !queryStack ) in
				let unused = possibilitiesStack := []::!possibilitiesStack in
			try
				answerTracker ()
			with Exhausted -> answerTracker()
			else
				let flag = ref true in
				let unifier = 
					try
						mgu v1 v2
					with NotUnif -> 
						let unused = flag := false in
						let unused = substitutionStack := List.tl !substitutionStack in
						let unused = namingStack := List.tl !namingStack in
						let unused = queryStack := List.tl !queryStack in
						id
				in
			if !flag then 
				let unifier = composeSubstitutn ( List.hd !substitutionStack ) unifier in
				let unused = substitutionStack := unifier::!substitutionStack in
				let unused = namingStack := ( List.hd !namingStack )::!namingStack in
				let first = List.tl ( List.hd !queryStack ) in
				let first = if ( List.length first = 0 ) then [] else ( applySubstitutionOnComponent unifier ( List.hd first ) )::List.tl first in
				let unused = queryStack := first::( !queryStack ) in
				let unused = possibilitiesStack := []::!possibilitiesStack in
				try
					answerTracker()
				with Exhausted -> answerTracker ()
			else raise Exhausted
			
	|	SUBASSGNCOMP( SUBASSGN( v3, NUMTERM( n1 ), NUMTERM( n2 ) ) ) -> if ( List.hd !possibilitiesStack = [] && List.length !queryStack = List.length !possibilitiesStack )
		then
			let unused = possibilitiesStack :=  List.tl !possibilitiesStack in
			let unused = substitutionStack := List.tl !substitutionStack in
			let unused = namingStack := List.tl !namingStack in
			let unused = queryStack := List.tl !queryStack in
			raise Exhausted
		else
			let newRule = Hashtbl.create 1 in
			let unused = Hashtbl.add newRule v3 (NUMTERM( n1 - n2 ) ) in
			let sigma = defineSubstitutionUHE newRule in
			let sigma = composeSubstitutn ( List.hd !substitutionStack ) sigma in
			let unused = substitutionStack := sigma::!substitutionStack in
			let unused = namingStack := ( List.hd !namingStack )::!namingStack in
			let first = List.tl ( List.hd !queryStack ) in
			let first = if ( List.length first = 0 ) then [] else ( applySubstitutionOnComponent sigma ( List.hd first ) )::List.tl first in
			let unused = queryStack := first::( !queryStack ) in
			let unused = possibilitiesStack := []::!possibilitiesStack in
			try
				answerTracker()
			with Exhausted -> answerTracker()
;;

let rec answerer flag query = 
	let unused = if flag then queryStack := [query]::!queryStack else () in
	let unused = if flag then substitutionStack := id::!substitutionStack else () in
	let unused = if flag then renameVars id [query] else [] in

	let rec answerPrinter vars mappedVars = match ( vars, mappedVars ) with
	| ( [], [] ) -> ""
	| ( ( VARTERM( Var ( v ) ) )::bd1, ( PREDTERM( Pred( p ) ) )::bd2 ) -> ( v^":- "^p^"\n" )^( answerPrinter bd1 bd2 )
	| ( ( VARTERM( Var ( v ) ) )::bd1, ( NUMTERM( n ) )::bd2 ) ->  ( v^":- "^( string_of_int n )^"\n" )^( answerPrinter bd1 bd2 )
	| ( t1::bd1, t2::bd2 ) -> ( answerPrinter bd1 bd2 )
	in
	
	try
		answerTracker () ; ""
	with 
	| AnswerFound ->
		let vars = variables query in
		let sigma = List.hd !substitutionStack in
		let unused = queryStack := List.tl !queryStack in
		let unused = substitutionStack := List.tl !substitutionStack in
		let unused = namingStack := List.tl !namingStack in
		let mappedVars = List.map sigma vars in
		if ( answerPrinter vars mappedVars ) = "" then "true\n" else ( answerPrinter vars mappedVars )
	| Exhausted -> answerer false query
;;

let destruct () = 
	let unused = substitutionStack :=  [] in
	let unused = namingStack :=  [] in
	let unused = queryStack :=  [] in
	let unused = possibilitiesStack :=  [] in
	""
;;

let fileparser fl = 
		let lexbuf = Lexing.from_channel ( open_in fl ) in
		try
			input token lexbuf ; ""
		with End_of_file -> ""
;;