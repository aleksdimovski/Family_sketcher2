(***************************************************)
(*                                                 *)
(*    Forward/Backward Single Analysis Iterator    *)
(*                                                 *)
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
open Functions
open Domain

module SingleAnalysisIterator (B: PARTITION) (D: RANKING_FUNCTION) =
struct

  module B = B
  module D = D  

  let fwdInvMap = ref InvMap.empty

  let addFwdInv l (a:B.t) = fwdInvMap := InvMap.add l a !fwdInvMap

  let fwdMap_print fmt m = InvMap.iter (fun l a -> 
      Format.fprintf fmt "%a: %a\n" label_print l B.print a) m

  let result = ref "assert CORRECT"


  let bwdInvMap = ref InvMap.empty

  let addBwdInv l (a:D.t) = bwdInvMap := InvMap.add l a !bwdInvMap

  let bwdMap_print fmt m = InvMap.iter (fun l a -> 
      Format.fprintf fmt "%a: %a\n" label_print l D.print a) m

  (* Forward Iterator *)

  let rec fwdStm funcs env vars config p s =
    match s with
    | A_label _ -> p
    | A_return -> B.bot env vars
    | A_assign ((l,_),(e,_)) -> let e1 = aExp_simplify e config in B.fwdAssign p (l,e1)
    | A_assert (b,ba) ->
		  let (b,ba) = (bExp_simplify b config, ba) in
	      let p2' = (B.filter p b) in
      	  let p2 = B.filter p (fst (negBExp (b,ba))) in 
		  if ((B.isLeq p p2') && not (B.isBot p)) then (Format.fprintf !fmt "\nassert (%a) CORRECT\n" bExp_print_aux b; result:="assert CORRECT"; p2')
		  else (if (B.isBot p2') then (Format.fprintf !fmt "\nassert (%a) ERROR:\n %a\n" bExp_print_aux b B.print p2; result:="assert ERROR"; p2') 
				else (if (not (B.isBot p2)) then (Format.fprintf !fmt "\nassert (%a) ERROR:\n %a\n" bExp_print_aux b B.print p2; result:="assert ERROR"; p2') 
		  			  else (Format.fprintf !fmt "\nassert (%a) DONT KNOW\n" bExp_print_aux b; result:="assert DONT KNOW"; p2') ) )
    | A_if ((b,ba),s1,s2) ->
	  let (b,ba) = (bExp_simplify b config, ba) in
	  let p1 = B.filter p b in 
      let p1' = fwdBlk funcs env vars config p1 s1 in
      let p2 = B.filter p (fst (negBExp (b,ba))) in
      let p2' = fwdBlk funcs env vars config p2 s2 in 
	  (*Format.fprintf !fmt "\n filter(%a,%a) p1 = (%a), p1' = (%a), p2 = (%a), p2' = (%a):\n" B.print p bExp_print_aux b B.print p1 B.print p1' B.print p2 B.print p2';*)
      B.join p1' p2'
    | A_ifdef ((b,ba),s1,s2) -> p  
    | A_while (l,(b,ba),s) ->
	  let p_in = p in 	
	  let (b,ba) = (bExp_simplify b config, ba) in
      let rec aux i p2 n =
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
          aux i'' (fwdBlk funcs env vars config (B.filter i'' b) s) (n+1)
      in
      let i = B.bot env vars in
      let p2 = fwdBlk funcs env vars config (B.filter i b) s in 
	  (*Format.fprintf !fmt "\n in while: p2 = %a:\n" B.print p2; *)
      let p = aux i p2 1 in 
	  (*Format.fprintf !fmt "\n in while: p = %a:\n" B.print p; *)
	  let p_down = fwdBlk funcs env vars config (B.filter p b) s in   (* this line is added additionally: performs narrowing  *)
      (*Format.fprintf !fmt "\n in while: p_down = %a:\n" B.print p_down;*)
	  let notb = fst (negBExp (b,ba)) in 
      addFwdInv l p_down; 
	  let p_final = B.join (B.filter p_in notb) (B.filter p_down notb) in 
	  Format.fprintf !fmt "\n in while: p_top %a = p1 %a :: p2 %a:\n" B.print (B.filter (B.top env vars) notb) B.print (B.filter p_in notb) B.print (B.filter p_down notb); 
	  p_final
      (* addFwdInv l p; B.filterSingle p (fst (negBExp (b,ba))) config *)
    | A_call (f,ss) ->
      let f = StringMap.find f funcs in
      let p = List.fold_left (fun ap (s,_) -> 
          fwdStm funcs env vars config p s) p ss in
      fwdBlk funcs env vars config p f.funcBody
    | A_recall (f,ss) -> B.top env vars (* TODO *)

  and fwdBlk funcs env vars config (p:B.t) (b:block) : B.t =
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
      fwdBlk funcs env vars config (fwdStm funcs env vars config p s) b


  (* Backward Iterator + Recursion *)

  let rec bwdStm ?domain funcs env vars config (p,r,flag) s =
    match s with
    | A_label _ -> (p,r,flag)
    | A_return -> D.zero ?domain:domain env vars, r, flag
    | A_assign ((l,_),(e,_)) ->  let e1 = aExp_simplify e config in 
      D.bwdAssign ?domain:domain p (l, e1), r, flag
    | A_assert (b,_) -> p, r, flag
    | A_if ((b,ba),s1,s2) ->
      let (p1, _, flag1) = bwdBlk funcs env vars config (p, r, flag) s1 in 
	  let b = bExp_simplify b config in 
      let p1 = D.filter ?domain:domain p1 b in					
      let (p2, _, flag2) = bwdBlk funcs env vars config (p, r, flag) s2 in
      let p2 = D.filter ?domain:domain p2 (fst (negBExp (b, ba))) in
      if !tracebwd && not !minimal then begin
        Format.fprintf !fmt "p1: %a\n" D.print p1;
        Format.fprintf !fmt "p2: %a\n" D.print p2
      end;
      (D.join APPROXIMATION p1 p2, r, flag1 || flag2)
    | A_while (l, (b, ba), s) ->
      (*let a = InvMap.find l !fwdInvMap in
      let dm = if !refine then Some a else None in  *)
	  let b = bExp_simplify b config in 
      let p1 = D.filter p (fst (negBExp (b, ba))) in
      let rec aux (i, _, _) (p2, _, flag2) n =
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
                bwdBlk funcs env vars config (i'', r, flag2) s in
              let p2' = D.filter p2 b in
              aux (i'', r, flag2) (p2', r, flag2) (n + 1)
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
              bwdBlk funcs env vars config (i'', r, flag2) s in 
            let p2' = D.filter p2 b in
            aux (i'', r, flag2) (p2', r, flag2) (n + 1)
      in
      let i = (D.bot env vars, r, flag) in
      let (p2, _, flag2) = bwdBlk funcs env vars config i s in
      let p2' = D.filter p2 b in
      let (p, r, flag) = aux i (p2', r, flag2) 1 in
      addBwdInv l p;
      (*if !refine then
        (D.refine p a, r, flag)
      else  *)
        (p, r, flag)
    | A_call (f, ss) ->
      let f = StringMap.find f funcs in
      let p = bwdRec funcs env vars config p f.funcBody in
      List.fold_left (fun (ap, ar, aflag) (s, _) ->
          bwdStm ?domain:domain funcs env vars config (ap, ar, aflag) s
        ) (p, r, flag) ss
    | A_recall (f, ss) ->
      (match domain with
       | None ->
         List.fold_left (fun (ap, ar, aflag) (s, _) ->
             bwdStm funcs env vars config (ap, ar, aflag) s
           ) (D.join APPROXIMATION p r, r, true) ss
       | Some domain ->
         List.fold_left (fun (ap, ar, aflag) (s, _) ->
             bwdStm ~domain:domain funcs env vars config (ap, ar, aflag) s
           ) (r, r, true) ss)

  and bwdBlk funcs env vars config (p,r,flag) (b:block) : D.t * D.t * bool =
    let result_print l p =
      Format.fprintf !fmt "### %a ###:\n%a@." label_print l D.print p
    in
    match b with
    | A_empty l ->
      (*let a = InvMap.find l !fwdInvMap in
      let p = if !refine then D.refine p a else p in *)
      if !tracebwd && not !minimal then result_print l p;
      addBwdInv l p; (p,r,flag)
    | A_block (l,(s,_),b) ->
      stop := Sys.time ();
      if ((!stop -. !start) > !timeout)
      then raise Timeout
      else
        let (b,rb,flagb) = bwdBlk funcs env vars config (p,r,flag) b in
        (*let a = InvMap.find l !fwdInvMap in *)
        let (p,r,flag) = if !refine then 
            bwdStm funcs env vars config (b,rb,flagb) s 
          else bwdStm funcs env vars config (b,rb,flagb) s in
        (*let p = if !refine then D.refine p a else p in *)
        if !tracebwd && not !minimal then result_print l p;
        addBwdInv l p; (p,r,flag)

  and bwdRec funcs env vars config (p:D.t) (b:block) : D.t = 
    let (res, _, _) = bwdBlk funcs env vars config (p,D.bot env vars,false) b  in
    res


  let rec initStm env vars s =
    match s with
    | A_if (_,s1,s2) -> initBlk env vars s1; initBlk env vars s2
    | A_while (l,_,s) -> 
      addBwdInv l (D.bot env vars); initBlk env vars s
    | _ -> ()

  and	initBlk env vars b =
    match b with
    | A_empty l -> addBwdInv l (D.bot env vars)
    | A_block (l,(s,_),b) -> addBwdInv l (D.bot env vars); 
      initStm env vars s; initBlk env vars b
	  

  (* Analyzer *)


(* IMPORTANT FUNCTION THAT DOES THE ANALYSIS*)
  let analyze (vars,stmts,funcs) main config (* determines the current configuration *)=
    let rec aux xs env = match xs with
      | [] -> env
      | x::xs -> 
        aux xs (Environment.add env [|(Var.of_string x.varId)|] [||])
    in
    let f = StringMap.find main funcs in
    let v1 = snd (List.split (StringMap.bindings vars)) in
    let v2 = snd (List.split (StringMap.bindings f.funcVars)) in
    let vars = List.append v1 v2 in
    let env = aux vars (Environment.make [||] [||]) in
    let s = f.funcBody in
    (*initBlk env vars stmts; initBlk env vars s; *)
    (* TODO: handle functions calls *)
    (* Forward Analysis *)
    if !tracefwd && not !minimal then
      Format.fprintf !fmt "\nForward Analysis Trace:\n";
    let startfwd = Sys.time () in
    let state = fwdBlk funcs env vars config (fwdBlk funcs env vars config (B.top env vars) stmts) s in
    let stopfwd = Sys.time () in
    if not !minimal then
      begin
        if !timefwd then
          Format.fprintf !fmt "\nForward Analysis (Time: %f s):\n" (stopfwd-.startfwd)
        else
          Format.fprintf !fmt "\nForward Analysis:\n";
        fwdMap_print !fmt !fwdInvMap;
      end;
	let rank = ref (D.bot env vars) in
	(*if (String.equal !result "assert CORRECT") then ( *)
    	(* Backward Analysis *)
    	if !tracebwd && not !minimal then
      		Format.fprintf !fmt "\nBackward Analysis Trace:\n";
    	start := Sys.time ();
    	let startbwd = Sys.time () in
    	let i = bwdRec funcs env vars config (bwdRec funcs env vars config (D.zero env vars) s) stmts in
    	let stopbwd = Sys.time () in
    	if not !minimal then begin
      		if !timebwd then
        		Format.fprintf !fmt "\nBackward Analysis (Time: %f s):\n" (stopbwd-.startbwd)
      		else
        		Format.fprintf !fmt "\nBackward Analysis:\n";
      	bwdMap_print !fmt !bwdInvMap;
    	end;
    	let b = D.defined i in 
		Format.fprintf !fmt "Defined: %b :: \nRanking function is: \n%a\n" b D.print (InvMap.find 1 !bwdInvMap); 
		rank := InvMap.find 1 !bwdInvMap;
		if (not b) then result := "assert ERROR"; 
	(*); *)
	!result

end
