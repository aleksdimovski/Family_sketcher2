(***************************************************)
(*                                                 *)
(*    Forward/Backward DT Analysis Iterator        *)
(*            Program Sketcher                     *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open AbstractSyntax
open InvMap
open Apron
open Iterator
open Partition
open DTDomain
open ItoA
open Constraints
open SketchDomainRF

module DTAnalysisIterator (B: DTDomain) (D: SketchDomainRF) =
struct

  module B = B
  module P = B.P
  module C = P.C

  module D = D 
  module R = D.R 
  module S = R.B
  module T = D.P


  let fwdInvMap = ref InvMap.empty
  let addFwdInv l (a:B.t) = fwdInvMap := InvMap.add l a !fwdInvMap
  let fwdMap_print fmt m = InvMap.iter (fun l a -> 
      Format.fprintf fmt "%a: %a\n" label_print l B.print a) m

  module ExpMap = Map.Make(struct type t=bExp let compare=compare end)

  let assertExpMap = ref ExpMap.empty
  let addAssertInv (b:bExp) ((a1,a2,a3):B.t*B.t*bool) = assertExpMap := ExpMap.add b (a1,a2,a3) !assertExpMap
  let assertMap_print fmt m = ExpMap.iter (fun b (a1,a2,a3) -> 
      (*Format.fprintf fmt "\nAssertion (%a): %a\n" bExp_print_aux b *)
	  B.print_assert fmt a1 a2 a3) m

  let assertMap_print_correct fmt m = ExpMap.iter (fun b (a1,a2,a3) -> 
      (*Format.fprintf fmt "\nAssertion (%a): %a\n" bExp_print_aux b *)
	  B.print_assert_correct fmt a1 a2 a3) m


  let bwdInvMap = ref InvMap.empty

  let addBwdInv l (a:D.t) = bwdInvMap := InvMap.add l a !bwdInvMap

  let bwdMap_print fmt m = InvMap.iter (fun l a -> 
      Format.fprintf fmt "%a: %a\n" label_print l D.print a) m  


  (* Forward Iterator *)

  let rec fwdStm funcs env_vars env_feats vars feats p s =
    match s with
    | A_label _ -> p
    | A_return -> B.bot env_vars env_feats vars feats
    | A_assign ((l,la),(e,ea)) -> let featsIn = (AbstractSyntax.aExp_hasNoFeat e feats true) in 
								if ((List.length featsIn) > 0) then 
									(let pin = ref p in
									 (*let pout = ref (B.bot env_vars env_feats vars feats) in 
									 let cons_list = ref [[]] in 
									 let pin_list = ref [p] in *)
									 List.iter (fun (x,y) -> (*Format.fprintf !fmt "Feature %s isLin %b \n" x.varName y; *)
									 				if (y==false) then (
													(*let cons_temp = ref [] in 
													let pin_temp = ref [] in 		*)											
									 				let fm = StringMap.find x.varName !ItoA.features in 
									 				let dom = fm.featDom in 
													pin := B.bot env_vars env_feats vars feats; 
													(*let pin2 = ref p in  *)
									 				for i = 0 to (List.length dom)-1 do														
														let b1 = 
														if (i==0) then (A_rbinary (A_LESS_EQUAL,(A_var x,(Lexing.dummy_pos,Lexing.dummy_pos)),(A_const (List.nth dom i), (Lexing.dummy_pos,Lexing.dummy_pos))) (*in 
																	    pin := B.config_filter p b1; *)																																
																		(*Format.fprintf !fmt "Exp R %a" aExp_print (e,ea); 
																		Format.fprintf !fmt "Exp L %a" aExp_print (l,la); 
																		Format.fprintf !fmt "\n p = : %a \n" B.print p;
																		Format.fprintf !fmt "\n p2 = : %a \n" B.print p2; *)
																		)
														else if (i==(List.length dom)-1) then (A_rbinary (A_GREATER_EQUAL,(A_var x,ea),(A_const (List.nth dom i), ea)) (*in 
																	    					   pin := B.config_filter p b1; *)
																		)
															 else (*(A_rbinary (A_LESS_EQUAL,(A_var x,ea),(A_const (List.nth dom i), ea)))  *)
															 (A_bbinary (A_AND, (A_rbinary (A_LESS_EQUAL,(A_var x,ea),(A_const (List.nth dom i), ea)), ea), (A_rbinary (A_GREATER_EQUAL,(A_var x,ea),(A_const (List.nth dom i), ea)), ea)) ) 
															 (*in 
																   pin := B.config_filter p b1; *)
																		 in 
														(*pin_temp := !pin_temp@List.map (fun el -> B.config_filter el b1) !pin_list;	*)
														(*Format.fprintf !fmt "\n Trees before : %a " B.print !pin2; *)
														(*if (i!=(List.length dom)-1) then pin2 := B.config_filter2 !pin2 b1; *)
														(*Format.fprintf !fmt "\n Trees after: %a " B.print !pin2;*)
														(*pin_temp := !pin_temp@List.map (fun el -> el) !pin_list; *)
														let cons = Lincons1.make (Linexpr1.make env_vars) Lincons1.EQ in
  											   			Lincons1.set_array cons [| ((Coeff.s_of_int 1), (Var.of_string x.varId)) |] (Some (Coeff.s_of_int (-(List.nth dom i))));
														(*let cons2 = Lincons1.make (Linexpr1.make env_feats) Lincons1.EQ in
  											   			Lincons1.set_array cons2 [| ((Coeff.s_of_int 1), (Var.of_string x.varId)) |] (Some (Coeff.s_of_int (-(List.nth dom i))));*)														
														(*cons_temp := !cons_temp@List.map (fun el -> el@[cons]) !cons_list; PRESENT *)
														(*let tree_temp = B.config_filter p b1 in *)
														(*pin2 := B.add_constraint2 !pin2 cons cons2; *)
														(*Format.fprintf !fmt "\n Trees after cons: %a " B.print !pin2;*)
														
														let p_out = B.config_filter_constraint p b1 (P.inner env_vars vars [cons]) in 
														(*pin_temp := !pin_temp@[B.config_filter_constraint p b1 (P.inner env_vars vars [cons])];*)
														pin := B.join p_out !pin; 				
														(*pin := !pin2; *)
														
														(*cons_temp := !cons_temp@[[cons]]; *)
														 
														(*let p_cons = P.inner env_vars vars [cons] in 
														let p2 = B.add_constraint !pin p_cons in 	
														let p2' = B.fwdAssign p2 (l,e) in 
														let p2'' = B.remove_constraint p2' (Var.of_string x.varId) (Coeff.s_of_int (-(List.nth dom i))) in 
														(*Format.fprintf !fmt "\n assign p2' %a :\n p2'' %a \n" B.print p2' B.print p2''; *)
														pout := B.join p2'' !pout; *)
													done; (*cons_list := !cons_temp; pin_list := !pin_temp*) )
													) featsIn; 
													(*pout := B.bot env_vars env_feats vars feats;
													List.iter (fun el -> Format.fprintf !fmt "\n Constraint: %a " P.print (P.inner env_vars vars el); Format.fprintf !fmt "\n" ) !cons_list;
													List.iter (fun el -> Format.fprintf !fmt "\n Pin Trees: %a " B.print el; Format.fprintf !fmt "\n" ) !pin_list; 
													(*pin_list := List.map2 (fun x y -> B.add_constraint x (P.inner env_vars vars y)) !pin_list !cons_list;*)
													List.iter (fun el -> let p2' = B.fwdAssign el (l,e) in pout := B.join p2' !pout) !pin_list; *)
													(*Format.fprintf !fmt "\n assign pout: %a \n" B.print !pout;*) (*B.compress*) B.fwdAssign !pin (l,e) )
								 else B.fwdAssign p (l,e)
    | A_assert (b,ba) -> (*B.filter p b*)
		  let featsIn = (AbstractSyntax.bExp_hasNoFeat b feats true) in 
		  let hasFeat = ref false in 
	  	  let p2' = if ((List.length featsIn) > 0) then (hasFeat:=true; B.general_filter p b)
	      			else (B.filter p b) in
		  (*Format.fprintf !fmt "\nassert (%a) \n %a\n" B.print p B.print p2';*)
		  addAssertInv b (p,p2',!hasFeat); p2'
		  (* if (not (B.isBot p2)) then (Format.fprintf !fmt "\nassert (%a) \n %a\n" bExp_print_aux b B.print_assert p2; p2') 
		  else (Format.fprintf !fmt "\nassert (%a) CORRECT\n" bExp_print_aux b; p2') *)	
    | A_if ((b,ba),s1,s2) -> 
	  let featsIn = (AbstractSyntax.bExp_hasNoFeat b feats true) in 
	  if ((List.length featsIn) > 0) then (
	  	let p1 = B.general_filter p b in Format.fprintf !fmt "\n p1: %a \n" B.print p1;
      	let p1' = fwdBlk funcs env_vars env_feats vars feats p1 s1 in
      	let p2 = B.general_filter p (fst (negBExp (b,ba))) in Format.fprintf !fmt "\n p2: %a \n" B.print p2;
      	let p2' = fwdBlk funcs env_vars env_feats vars feats p2 s2 in
      	B.compress (B.join p1' p2')	  
	  )
	  else (
	  	let p1 = B.filter p b in 
      	let p1' = fwdBlk funcs env_vars env_feats vars feats p1 s1 in
      	let p2 = B.filter p (fst (negBExp (b,ba))) in
      	let p2' = fwdBlk funcs env_vars env_feats vars feats p2 s2 in
      	B.compress (B.join p1' p2') )
    | A_ifdef ((b,ba),s1,s2) ->	  
	  (*Format.fprintf !fmt "\n config-filter anal %d\n" 1;*)
	  let p1 = B.config_filter p b in 
      let p1' = fwdBlk funcs env_vars env_feats vars feats p1 s1 in 
	  (*let cst = (match b with | A_bvar v -> 0 | _ -> 1) in *)
	  let b_neg = fst (negBExp (b,ba)) in 
      let p2 = B.config_filter p b_neg in (*!AbstractSyntax.cst in AbstractSyntax.cst:=1; *)
      let p2' = fwdBlk funcs env_vars env_feats vars feats p2 s2 in
	  let pp = B.compress (B.join p1' p2') in 
	  (*Format.fprintf !fmt "\n ifdef p1=%a p1'=%a\n p2=%a p2'=%a \n" B.print p1 B.print p1' B.print p2 B.print p2';*) (*Format.fprintf !fmt "\n ifdef join %a \n" B.print (B.join p1' p2');
	  Format.fprintf !fmt "\n ifdef compress %a \n" B.print pp; *)
      pp		  
    | A_while (l,(b,ba),s) ->
      let rec aux i p2 n has =
        let i' = B.join p p2 in
        if !tracefwd && not !minimal then begin
          Format.fprintf !fmt "### %a:%i ###:\n" label_print l n;
          Format.fprintf !fmt "p1: %a\n" B.print p;
          Format.fprintf !fmt "i: %a\n" B.print i;
          Format.fprintf !fmt "p2: %a\n" B.print p2;
          Format.fprintf !fmt "i': %a\n" B.print i'
        end;
        if B.isLeq i' i then i else
          let i'' = if n <= !joinfwd then i' else 
              B.widen i (B.join i i') in
          if !tracefwd && not !minimal then
            Format.fprintf !fmt "i'': %a\n" B.print i'';
		  let b' = if (has) then B.general_filter i'' b else B.filter i'' b in 
          aux i'' (fwdBlk funcs env_vars env_feats vars feats b' s) (n+1) has
      in
	  let featsIn = (AbstractSyntax.bExp_hasNoFeat b feats true) in 
	  let hasFeat = ref false in 
	  if ((List.length featsIn) > 0) then hasFeat:=true; 
      let i = B.bot env_vars env_feats vars feats in
      let p2 = fwdBlk funcs env_vars env_feats vars feats (B.filter i b) s in 
      let p = aux i p2 1 !hasFeat in 
	  Format.fprintf !fmt "after while p: %a\n" B.print p;
	  let p_down = fwdBlk funcs env_vars env_feats vars feats (if (!hasFeat) then B.general_filter p b else B.filter p b) s in   (* this line is added additionally: performs narrowing  *)
	  (*Format.fprintf !fmt "narrow p_down: %a\n" B.print p_down; *)
	  (*let pp = if (!hasFeat) then B.general_filter2 p (fst (negBExp (b,ba))) else B.filter p (fst (negBExp (b,ba))) in 
	  Format.fprintf !fmt "pp: %a\n" B.print pp; *)
	  let p_down' = B.merge p_down (if (!hasFeat) then B.general_filter p (fst (negBExp (b,ba))) else B.filter p (fst (negBExp (b,ba)))) in (* this works for loo[1a-5.c*)
	  (*let p_down' = B.join p_down (if (!hasFeat) then B.general_filter p (fst (negBExp (b,ba))) else B.filter p (fst (negBExp (b,ba)))) in *)
	  (*let p_down' = p_down in *)
	  (*Format.fprintf !fmt "after narrow p_down': %a\n" B.print p_down'; *)
	  addFwdInv l p_down'; 
	  let p_end = if (!hasFeat) then B.general_filter p_down' (fst (negBExp (b,ba))) else B.filter p_down' (fst (negBExp (b,ba))) in 
	  (*Format.fprintf !fmt "p_end: %a\n" B.print p_end;  *)
	  B.compress (p_end)
    | A_call (f,ss) ->
      let f = StringMap.find f funcs in
      let p = List.fold_left (fun ap (s,_) -> 
          fwdStm funcs env_vars env_feats vars feats p s) p ss in
      fwdBlk funcs env_vars env_feats vars feats p f.funcBody
    | A_recall (f,ss) -> B.top env_vars env_feats vars feats (* TODO *) 
	| _ -> raise (Invalid_argument "\n Unhandled Statement\n")

  and fwdBlk funcs env_vars env_feats vars feats (p:B.t) (b:block) : B.t =
    let result_print l p =
      Format.fprintf !fmt "### %a ###: %a\n" label_print l B.print p
    in
    match b with
    | A_empty l ->
      if !tracefwd && not !minimal then result_print l p;
      addFwdInv l p; p
    | A_block (l,(s,_),b) ->
      if !tracefwd && not !minimal then result_print l p;
      addFwdInv l p; 
      fwdBlk funcs env_vars env_feats vars feats (fwdStm funcs env_vars env_feats vars feats p s) b



  (* Backward Iterator + Recursion *)


  let rec bwdStm funcs env_vars env_feats vars feats (p,r,flag) s =
    match s with
    | A_label _ -> (p,r,flag)
    | A_return -> p, r, flag
    | A_assign ((l,_),(e,ea)) -> let featsIn = (AbstractSyntax.aExp_hasNoFeat e feats true) in 
								if ((List.length featsIn) > 0) then 
									(let pin = ref p in
									let p_out = ref (D.bot env_vars env_feats vars feats) in
									 List.iter (fun (x,y) -> 
									 				if (y==false) then (									
									 				let fm = StringMap.find x.varName !ItoA.features in 
									 				let dom = fm.featDom in 
									 				for i = 0 to (List.length dom)-1 do		
													    pin := p; 
													    let config = [(x.varName,List.nth dom i)] in 
														let e1 = AbstractSyntax.aExp_simplify e config in													
														let b1 = 
														if (i==0) then (A_rbinary (A_LESS_EQUAL,(A_var x,(Lexing.dummy_pos,Lexing.dummy_pos)),(A_const (List.nth dom i), (Lexing.dummy_pos,Lexing.dummy_pos))) 	)												else if (i==(List.length dom)-1) then (A_rbinary (A_GREATER_EQUAL,(A_var x,ea),(A_const (List.nth dom i), ea)) )
															 else 
															 (A_bbinary (A_AND, (A_rbinary (A_LESS_EQUAL,(A_var x,ea),(A_const (List.nth dom i), ea)), ea), (A_rbinary (A_GREATER_EQUAL,(A_var x,ea),(A_const (List.nth dom i), ea)), ea)) ) 
																		 in 
														(*let cons = Lincons1.make (Linexpr1.make env_vars) Lincons1.EQ in
  											   			Lincons1.set_array cons [| ((Coeff.s_of_int 1), (Var.of_string x.varId)) |] (Some (Coeff.s_of_int (-(List.nth dom i))));
														let s = S.inner env_vars vars [cons] in 
														let r = R.bot ~domain:s env_vars vars in *)
														pin := D.config_filter !pin b1;
														(*Format.fprintf !fmt "### p_out %a ###:\n" D.print p_out;*)
														if (i==0) then p_out := D.bwdAssign !pin (l,e1) else p_out := D.join COMPUTATIONAL !p_out (D.bwdAssign !pin (l,e1)) 				
													done; ) else p_out := D.bwdAssign !pin (l,e)
													) featsIn; 
								 (*Format.fprintf !fmt "###asgn p_in %a ###:\n" D.print !pin;*)
								 !p_out, r, flag )
								 else (   match l,e with
  											| A_var x, A_URANDOM -> ( let b1 = A_rbinary (A_GREATER_EQUAL,(A_var x,(Lexing.dummy_pos,Lexing.dummy_pos)),(A_const 0, (Lexing.dummy_pos,Lexing.dummy_pos))) 
															 in D.compress(D.filter p b1), r, flag ) 
								 			| _, _ -> D.bwdAssign p (l,e), r, flag 
										)
    | A_assert (b,_) ->
		  (*let featsIn = (AbstractSyntax.bExp_hasNoFeat b feats true) in 
	  	  let p2' = if ((List.length featsIn) > 0) then (D.general_filter p b) else (D.filter p b) in
		  p2', r, flag *)
		  (*let p = D.filter p b in *)
		  p, r, flag
    | A_if ((b,ba),s1,s2) ->
	  let featsIn = (AbstractSyntax.bExp_hasNoFeat b feats true) in 
	  if ((List.length featsIn) > 0) then (
      	let (p1, _, flag1) = bwdBlk funcs env_vars env_feats vars feats (p, r, flag) s1 in
      	let p1 = D.general_filter p1 b in					
      	let (p2, _, flag2) = bwdBlk funcs env_vars env_feats vars feats (p, r, flag) s2 in
      	let p2 = D.general_filter p2 (fst (negBExp (b, ba))) in
      	(D.join APPROXIMATION p1 p2, r, flag1 || flag2) 
	  )
	  else (
      	let (p1, _, flag1) = bwdBlk funcs env_vars env_feats vars feats (p, r, flag) s1 in
      	let p1 = D.filter p1 b in					
      	let (p2, _, flag2) = bwdBlk funcs env_vars env_feats vars feats (p, r, flag) s2 in
      	let p2 = D.filter p2 (fst (negBExp (b, ba))) in
      	(D.join APPROXIMATION p1 p2, r, flag1 || flag2) )
    | A_ifdef ((b,ba),s1,s2) ->
      let (p1', _, flag1') = bwdBlk funcs env_vars env_feats vars feats (p, r, flag) s1 in
	  let p1 = D.config_filter p1' b in   
      let (p2', _, flag2') = bwdBlk funcs env_vars env_feats vars feats (p, r, flag) s2 in
	  let b_neg = fst (negBExp (b,ba)) in 
      let p2 = D.config_filter p2' b_neg in
      (D.join COMPUTATIONAL p1 p2, r, flag1' || flag2')	  
    | A_while (l, (b, ba), s) ->
      (*let a = InvMap.find l !fwdInvMap in
      let dm = if !refine then Some a else None in  *)
      let p1 = D.filter p (fst (negBExp (b, ba))) in
      let rec aux (i, _, _) (p2, _, flag2) n has =
        if !abort then raise Abort else
          let i' = D.join APPROXIMATION p1 p2 in
          if !tracebwd && not !minimal then begin
            Format.fprintf !fmt "### %a:%i ###:\n" label_print l n;
            Format.fprintf !fmt "p1: %a\n" D.print p1;
            Format.fprintf !fmt "i: %a\n" D.print i;
            Format.fprintf !fmt "p2: %a\n" D.print p2;
            Format.fprintf !fmt "i': %a\n" D.print i'
          end;
          let jokers = max 0 (!retrybwd * (!Ordinals.max + 1) - n + !joinbwd) in
          if (D.isLeq COMPUTATIONAL i' i) then
            if (D.isLeq APPROXIMATION i' i) then begin
              if !tracebwd && not !minimal then begin
                Format.fprintf !fmt "### %a:FIXPOINT ###:\n" label_print l;
                Format.fprintf !fmt "i: %a\n" D.print i
              end;
              (i, r, flag2)
            end else begin
              let i'' =
                if n <= !joinbwd then
                  i'
                else
                  D.widen ~jokers:jokers i i'
              in
              if !tracebwd && not !minimal then
                Format.fprintf !fmt "i'': %a\n" D.print i'';
              let (p2, _, flag2) = 
                bwdBlk funcs env_vars env_feats vars feats (i'', r, flag2) s in 	
              let p2' = if (has) then D.general_filter p2 b else D.filter p2 b in  
              aux (i'', r, flag2) (p2', r, flag2) (n + 1) has 
            end
          else
            let i'' =
              if n <= !joinbwd then
                i'
              else
                D.widen ~jokers:jokers i
                  (D.join COMPUTATIONAL i i')
            in
            if !tracebwd && not !minimal then
              Format.fprintf !fmt "i'': %a\n" D.print i'';
            let (p2, _, flag2) = 
              bwdBlk funcs env_vars env_feats vars feats (i'', r, flag2) s in
            let p2' = if (has) then D.general_filter p2 b else D.filter p2 b in 	
            aux (i'', r, flag2) (p2', r, flag2) (n + 1) has 
      in
	  let featsIn = (AbstractSyntax.bExp_hasNoFeat b feats true) in 
	  let hasFeat = ref false in 
	  if ((List.length featsIn) > 0) then hasFeat:=true; 	  
	  
      let i = (D.bot env_vars env_feats vars feats, r, flag) in
      let (p2, _, flag2) = bwdBlk funcs env_vars env_feats vars feats i s in
      let p2' = (*if (!hasFeat) then D.general_filter p2 b else*) D.filter p2 b in 
      let (p, r, flag) = aux i (p2', r, flag2) 1 !hasFeat in
      addBwdInv l p;
      (p, r, flag)
    | A_call (f, ss) ->
      let f = StringMap.find f funcs in
      let p = bwdRec funcs env_vars env_feats vars feats p f.funcBody in
      List.fold_left (fun (ap, ar, aflag) (s, _) ->
          bwdStm funcs env_vars env_feats vars feats (ap, ar, aflag) s
        ) (p, r, flag) ss
    | A_recall (f, ss) ->
      List.fold_left (fun (ap, ar, aflag) (s, _) ->
             bwdStm funcs env_vars env_feats vars feats (ap, ar, aflag) s) (D.join APPROXIMATION p r, r, true) ss

  and bwdBlk funcs env_vars env_feats vars feats (p,r,flag) (b:block) : D.t * D.t * bool =
    let result_print l p =
      Format.fprintf !fmt "### %a ###:\n%a@." label_print l D.print p
    in
    match b with
    | A_empty l ->
      (* let a = InvMap.find l !fwdInvMap in *)
      (*let p = if !refine then D.refine p a else p in*)
      if !tracebwd && not !minimal then result_print l p;
      addBwdInv l p; (p,r,flag)
    | A_block (l,(s,_),b) ->
      stop := Sys.time ();
      if ((!stop -. !start) > !timeout)
      then raise Timeout
      else
        let (b,rb,flagb) = bwdBlk funcs env_vars env_feats vars feats (p,r,flag) b in
        (*let a = InvMap.find l !fwdInvMap in *)
        let (p,r,flag) = if !refine then 
            bwdStm funcs env_vars env_feats vars feats (b,rb,flagb) s 
          else bwdStm funcs env_vars env_feats vars feats (b,rb,flagb) s in
        (*let p = if !refine then D.refine p a else p in *)
        if !tracebwd && not !minimal then result_print l p;
        addBwdInv l p; (p,r,flag)

  and bwdRec funcs env_vars env_feats vars feats (p:D.t) (b:block) : D.t = 
    let (res, _, _) = bwdBlk funcs env_vars env_feats vars feats (p,D.bot env_vars env_feats vars feats,false) b  in
    res


  let rec initStm env_vars env_feats vars feats s =
    match s with
    | A_if (_,s1,s2) -> initBlk env_vars env_feats vars feats s1; initBlk env_vars env_feats vars feats s2
    | A_while (l,_,s) -> 
      addBwdInv l (D.bot env_vars env_feats vars feats); initBlk env_vars env_feats vars feats s
    | _ -> ()

  and	initBlk env_vars env_feats vars feats b =
    match b with
    | A_empty l -> addBwdInv l (D.bot env_vars env_feats vars feats)
    | A_block (l,(s,_),b) -> addBwdInv l (D.bot env_vars env_feats vars feats); 
      initStm env_vars env_feats vars feats s; initBlk env_vars env_feats vars feats b


  (* Analyzer *)

(* this function generates all configurations *)
let rec process list = 
	if List.length list = 0 then [[]]
	else match list with
		| [] -> []
		| hd :: tl -> 
			let tmp = ref [] in
			let dom = hd.featDom in
			for i = 0 to (List.length dom)-1 do
				let tmp1 = List.map (fun l -> (hd.featName,List.nth dom i) :: l) (process tl) in 
				tmp := !tmp @ tmp1
			done;
			!tmp;;

(* this function generates all implicit constraints \Kk for features taking into account their domains *)
let rec process_cons feats_list env_feats ll = 
		match feats_list with
		| [] -> ll
		| hd :: tl ->
			let tmp = ref [] in
			let typ = hd.featTyp in
			if (typ <> A_BOOL) then (
				let dom = hd.featDom in
				let cons1 = Lincons1.make (Linexpr1.make env_feats) Lincons1.SUPEQ in
  				Lincons1.set_array cons1 [| ((Coeff.s_of_int 1), (Var.of_string hd.featId)) |] (Some (Coeff.s_of_int (-(List.nth dom 0))));
				let cons2 = Lincons1.make (Linexpr1.make env_feats) Lincons1.SUPEQ in
  				Lincons1.set_array cons2 [| ((Coeff.s_of_int (-1)), (Var.of_string hd.featId)) |] (Some (Coeff.s_of_int (List.nth dom ((List.length dom)-1))));				
				tmp := cons1::cons2::!tmp
			); 
			process_cons tl env_feats (!tmp @ ll)


	(*let result = ref [] in 
	List.iter (fun hd -> List.iter (fun vl -> (Format.fprintf !fmt "%s{%d}" hd.featName vl); let tmp = List.map (fun I -> (hd.featName,vl)::I) !result) hd.featDom) lista; 
	!result;;*)
			
let print_configs l =
  print_endline ""; Format.fprintf !fmt "Configurations: ";
  List.iter (fun el -> print_endline ""; List.iter (fun (key,v) -> Format.fprintf !fmt "% s{%d}, " key v) el) l;;  			



	let partition_toLatte (p:S.t) str liveVars feats =
		let lines = ref [] in
		let countVars = ref 0 in 
		let vars = ref [] in
		List.iter (fun v -> if (v.varName.[0]!='$') then (vars:=v::!vars; lines := !lines @ ["(declare-const " ^ v.varName ^ " Int)"])) liveVars;
		(*countLines := List.length (B.constraints p); (*print_list 1 (List.map (fun v -> v.varName) (B.varsLive p));*)
		print_string "len0 = "; print_int (!countLines); *)
		countVars := (List.length !vars) + 1;		
		let lin = S.to_stringLatte p !vars in
		List.iter (fun s -> lines := !lines @ [(s)]) lin;
		lines := !lines @ [(str)] @ ["(check-sat)"] @ ["(get-objectives)"];
		List.iter (fun s -> lines := !lines @ ["(eval " ^ s.varName ^ ")"]) feats;
		(*lines := !lines @ [("(check)")] @ [("(show-model)")]; *) 
		String.concat "\n" !lines;; 	

	let write_to_Lattefile file (p:S.t) str liveVars feats =
		let oc = open_out file in    						    (* create or truncate file, return channel *)
  		Printf.fprintf oc "%s\n" (partition_toLatte p str liveVars feats); 		(*(process_message message); *)   (* write something *)   
  		close_out oc;;

  	let read_process_lines command =
  		let lines = ref [] in
  		let in_channel = Unix.open_process_in command in
  		begin
    	try
      		while true do
        		lines := input_line in_channel :: !lines
      		done;
    	with End_of_file ->
      	ignore (Unix.close_process_in in_channel)
  		end;
  		List.rev !lines

	let rec print_list2 feats = function 
		[] -> () 
		| e::l -> let s = List.hd feats in Format.fprintf !fmt "\nHole {%s} is: %s " s.varName e; print_list2 (List.tl feats) l 

	let rec print_list feats = function 
		[] -> () 
		| [e] -> print_string " \n" ; print_string e
		| e1::e2::l -> if (e1="(objectives") then (let i1 = String.rindex e2 ' ' in let i2 = String.rindex e2 ')' in let s = String.sub e2 (i1+1) (i2-i1-1) in Format.fprintf !fmt "\nMinimal objective is: %s " s; print_list2 feats (List.tl l) ) else (print_list feats (e2::l))

	let rec process_list2 = function 
		[] -> [] 
		| e::l -> e::(process_list2 l) 

	let rec process_list = function 
		[] -> (1000,[]) 
		| [e] -> (1000,[])
		| e1::e2::l -> if (e1="(objectives") then (let i1 = String.rindex e2 ' ' in let i2 = String.rindex e2 ')' in let s1 = String.sub e2 (i1+1) (i2-i1-1) in let s2=process_list2 (List.tl l) in (int_of_string s1,s2) ) else (process_list (e2::l))

	let rec min_pos = function
  		| [] -> invalid_arg "min_pos"
  		| [x] -> (0, fst x)
  		| hd::tl ->	let p, v = min_pos tl in
    				if fst hd < v then (0, fst hd) else (p + 1, v)


(* IMPORTANT FUNCTION THAT DOES THE ANALYSIS*)
  let analyze (vars,stmts,funcs) main =
    let rec aux xs env = match xs with
      | [] -> env
      | x::xs -> 
        aux xs (Environment.add env [|(Var.of_string x.varId)|] [||])
    in
    let f = StringMap.find main funcs in
    let v1 = snd (List.split (StringMap.bindings vars)) in
    let v2 = snd (List.split (StringMap.bindings f.funcVars)) in
    let vars1 = List.append v1 v2 in
    (*let env_vars = aux vars (Environment.make [||] [||]) in*)
    let s = f.funcBody in
    (*initBlk env vars stmts; initBlk env vars s; *)
    (* TODO: handle functions calls *)
    (* Forward Analysis *)
    if !tracefwd && not !minimal then
      Format.fprintf !fmt "\nForward Analysis Trace:\n";
    let startfwd = Sys.time () in
	let feats = ref [] in
	let feats_feat = ref [] in
	let env_feats = ref (Environment.make [||] [||]) in 
	StringMap.iter (fun key value -> feats_feat := value :: !feats_feat; feats := {varId = value.featId; varName = value.featName; varTyp = value.featTyp} :: !feats; 
									env_feats :=  Environment.add !env_feats [|(Var.of_string value.featId)|] [||]) !ItoA.features; 
	(*let configs = process !feats_feat in print_configs configs; *)
	let vars = List.append vars1 !feats in 
    let env_vars = aux vars (Environment.make [||] [||]) in 	
	let constraints_list = process_cons !feats_feat !env_feats [] in 
	let part_list = P.inner !env_feats !feats constraints_list in (*print_string "GOO"; P.print !fmt part_list;*)
	let leaf_list = P.inner env_vars vars (process_cons !feats_feat env_vars []) in
    let state = fwdBlk funcs env_vars !env_feats vars !feats (fwdBlk funcs env_vars !env_feats vars !feats (B.initial ~domain:part_list leaf_list env_vars !env_feats vars !feats) stmts) s in
    let stopfwd = Sys.time () in
    if not !minimal then
      begin
        if !timefwd then
          Format.fprintf !fmt "\nForward Analysis (Time: %f s):\n" (stopfwd-.startfwd)
        else
          Format.fprintf !fmt "\nForward Analysis:\n";
        fwdMap_print !fmt !fwdInvMap;
      end;
	  if (!assertExpMap != ExpMap.empty) then 
	  	begin
			Format.fprintf !fmt "\nAssertion Analysis:\n"; 
			assertMap_print !fmt !assertExpMap;
		end;
	  (*Format.fprintf !fmt "\n\nAnalysis Result: ";
	  assertMap_print_correct !fmt !assertExpMap;  *)
	  
    (* Backward Analysis *)

    let find_correct m = 
	  	let tmp = ref [] in 
		ExpMap.iter (fun b (a1,a2,a3) -> tmp := !tmp@(B.find_correct a1 a2)) m; 
		!tmp in 

	let result = ref [] in 
	let forward_list = find_correct !assertExpMap in 
	let ll = (List.length forward_list) - 1 in 
	let ll1 = if (ll>2) then 1 else ll in  
	for count = 0 to ll1 do 

		let part_list = List.nth forward_list count in 
		(*Format.fprintf !fmt "\n Found P: %a" P.print part_list; *)
		let part_listT = T.inner !env_feats !feats (P.constraints part_list) in	
		(*Format.fprintf !fmt "\n Found T: %a" T.print part_listT;  *)
	
    	if !tracebwd && not !minimal then
      		Format.fprintf !fmt "\nBackward Analysis Trace:\n";
    	start := Sys.time ();
    	let startbwd = Sys.time () in
    	let i = bwdRec funcs env_vars !env_feats vars !feats (bwdRec funcs env_vars !env_feats vars !feats (D.zero ~domain:part_listT env_vars !env_feats vars !feats) s) stmts in
    	let stopbwd = Sys.time () in
    	if not !minimal then begin
      		if !timebwd then
        		Format.fprintf !fmt "\nBackward Analysis (Time: %f s):\n" (stopbwd-.startbwd)
      		else
        		Format.fprintf !fmt "\n\nBackward Analysis %d:\n" (count+1);
      	bwdMap_print !fmt !bwdInvMap;
    	end;
    	(*let b = D.defined i in 
		Format.fprintf !fmt "defined {%b}\n " b;
		Format.fprintf !fmt "Ranking function is: \n%a\n" D.print (InvMap.find 1 !bwdInvMap); 
		Format.fprintf !fmt "\nTermination Result: ";
		let nn = D.print_terminate !fmt i in   *)
		let slist = D.result_terminate i in 
		let solution = ref [] in 
		List.iter (fun (el1,el2) -> (*Format.fprintf !fmt "\n LisT: %a" S.print el1; Format.fprintf !fmt " : %s\n" el2; *)
								let file = "latte" in 
								write_to_Lattefile file el1 el2 vars !feats; 
								let l2 = read_process_lines ("z3 "^(file)) in 
								solution := !solution@[process_list l2]) slist; 
		(*Format.fprintf !fmt "\nThe length of solution is: %d " nn; *)
		let (s1,s2) = 
		if ((List.length !solution) = 0) then (-1,[]) 
		else  let (pos,min) = min_pos !solution in (List.nth !solution pos) in 
		(*if (s1 != -1) then *)result := !result@[(part_list,InvMap.find 1 !bwdInvMap,s1,s2)];
	done;

	List.iter ( fun (sol,rank,s1,s2) -> 
			Format.fprintf !fmt "\n\nSolution: %a" P.print sol; 
			Format.fprintf !fmt "\nRanking function is: \n%a" D.print rank; 
			Format.fprintf !fmt "\nMinimal objective is: %d " s1;
			List.iter2 (fun e1 e2 -> Format.fprintf !fmt "\nHole {%s} is: %s " e2.varName e1) s2 !feats ) !result; 
			
	true

end
