Require Export Arrow Init.


Parameter fi' : indiv_choice_func.
Axiom R'D : (profile fi' H) ∈ D.
Axiom fi'_prop : 
  forall (fi : indiv_choice_func) top bot x i, 
  i ∈ H -> (bot,top) ∈ (P (fi' i)) /\
  ((forall y, y ∈ X -> (x,y) ∈ (fi i) <-> (x,y) ∈ (fi' i)) /\ 
   (forall y, y ∈ X -> (y,x) ∈ (fi i) <->  (y,x) ∈ (fi' i))).

    
Lemma extreme :
  forall f, U f -> WP f -> IIA f -> 
  (forall x (fi : indiv_choice_func), x ∈ X -> (profile fi H) ∈ D ->
  (forall i, i ∈ H -> 
    (forall y, y ∈ X -> (x,y) ∈ (fi i)) \/ 
    (forall y, y ∈ X -> (y,x) ∈ (fi i))) ->
  (forall y, y ∈ X -> (x,y) ∈ (f (profile fi H))) \/ 
  (forall y, y ∈ X -> (y,x) ∈ (f (profile fi H) ))).
Proof.
  move => f Uf WPf IIAf x fi xX RD H0.

  (* order (f (profile fi H)) *)
  move : (Uf fi RD)  => Uf_.
  rewrite in_set in Uf_.
  case /andP : Uf_ => [_ ord].
  move /orderP : ord => [refl [comp trans]].

  (* order (f (profile fi' H)) *)
  move : (Uf fi' R'D) => Uf'.
  rewrite in_set in Uf'.
  case /andP : Uf' => [_ ord].
  move /orderP : ord => [refl' [comp' trans']].

  (* Assume existstance top and bot  *)
  apply NNPP => F.
  move /not_or_and : F => [L R].
  move /not_all_ex_not : L => [top L].
  move /not_all_ex_not : R => [bot R].
  move /(imply_to_and (top ∈ X) _) : L => [topX _xRtop].
  move /(imply_to_and (bot ∈ X) _) : R => [botX _botRx].

  (* property of fi' *)
  move : (fi'_prop fi top bot x) => fi'_p.

  (* x <> top, x <> bot, top <> bot *)
  have _xtop : top <> x.
    move => F; subst top.
    case (_xRtop (refl x)).  
  have _xbot : x <> bot.
    move => F; subst bot.
    case (_botRx (refl x)).
  have _topbot : top <> bot.
    move => F; subst bot.
    move : (comp top x _xtop).
    case /orP => F.
    case (_botRx F).
    case (_xRtop F).
    
  (* (top, x) ∈ (f (profile fi H)) *)
  have top_x_R : (top, x) ∈ (f (profile fi H)).
    move : (comp top x _xtop).
    case /orP => //.
  
  (* (top, x) ∈ (f (profile fi H)) *)
  have x_bot_R : (x,bot) ∈ (f (profile fi H)).
    move : (comp x bot _xbot).
    case /orP => //.

  (* (bot,top) ∈ (f (profile fi' H)) *)
  have bot_top_R' : (bot,top) ∈ (P (f (profile fi' H))).
    apply : (WPf fi' bot top R'D botX topX).
    move => i iH.
    apply  (fi'_p i iH).

  (* (top,x) ∈ (f (profile fi' H)) *)
  have top_x_R' : (top,x) ∈ (f (profile fi' H)).
    suff H2 : ((top,x) ∈ (f (profile fi H)) <-> (top,x) ∈ (f (profile fi' H))) /\ 
              ((x,top) ∈ (f (profile fi H)) <-> (x,top) ∈ (f (profile fi' H))).
      move : H2 => [H2 _].
      rewrite -H2 => //.
    apply:  (IIAf fi fi' top x RD R'D topX xX).
    move => i iH.
    move : (fi'_p i iH) => [bot_top_PRi' [max min]].
    move : (max top topX).
    move : (min top topX).
    done.
  
  (* (x,bot) ∈ (f (profile fi' H)) *)
  have x_bot_R' : (x,bot) ∈ (f (profile fi' H)).
    suff H2 : ((bot,x) ∈ (f (profile fi H)) <-> (bot,x) ∈ (f (profile fi' H))) /\ 
              ((x,bot) ∈ (f (profile fi H)) <-> (x,bot) ∈ (f (profile fi' H))).
      move : H2 => [_ H2].
      rewrite -H2 => //.
    apply:  (IIAf fi fi' bot x RD R'D botX xX).
    move => i iH.
    move : (fi'_p i iH) => [bot_top_PRi' [max min]].
    move : (max bot botX).
    move : (min bot botX).
    done.
  
  rewrite in_set in bot_top_R'.
  move /andP : bot_top_R' => /= [_ F].
  move : (trans' top x bot top_x_R' x_bot_R') => top_bot_R'.
  rewrite top_bot_R' in F.
  apply negb_true_iff in F.
  apply diff_true_false => //.
Qed.  


  
  
  
  





  
 

  

  





    



            


  