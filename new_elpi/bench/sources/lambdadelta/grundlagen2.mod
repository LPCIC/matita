module grundlagen2.

accumulate grundlagen.


% constant 256
g+line2 l_e_bij_th1 6744
       (abst l+2 (sort k+set) nsigma\ (abst l+2 (sort k+set) tau\ (abst l+2 (sort k+set) upsilon\ (abst l+2 (abst l+1 nsigma x\ tau) f\ (abst l+2 (abst l+1 tau x\ upsilon) g\ (abst l+2 (appr f (appr tau (appr nsigma l_e_bijective))) bf\ (abst l+2 (appr g (appr upsilon (appr tau l_e_bijective))) bg\ (cast (appr (abst l+2 nsigma x\ (appr (appr x f) g)) (appr upsilon (appr nsigma l_e_bijective))) (appr (appr bg (appr bf (appr g (appr f (appr upsilon (appr tau (appr nsigma l_e_bij_t2))))))) (appr (appr bg (appr bf (appr g (appr f (appr upsilon (appr tau (appr nsigma l_e_bij_t1))))))) (appr (appr (appr bg (appr bf (appr g (appr f (appr upsilon (appr tau (appr nsigma l_e_bij_h))))))) (appr upsilon (appr nsigma l_e_surjective))) (appr (appr (appr bg (appr bf (appr g (appr f (appr upsilon (appr tau (appr nsigma l_e_bij_h))))))) (appr upsilon (appr nsigma l_e_injective))) l_andi))))))))))))
.

g+line2 l_e_fise 6743
       (abst l+2 (sort k+set) nsigma\ (abst l+2 (sort k+set) tau\ (abst l+2 (abst l+1 nsigma x\ tau) f\ (abst l+2 (abst l+1 nsigma x\ tau) g\ (abst l+2 (appr g (appr f (appr (abst l+1 nsigma x\ tau) l_e_is))) i\ (abst l+2 nsigma s\ (cast (appr (appr s g) (appr (appr s f) (appr tau l_e_is))) (appr i (appr (appr (appr s f) (appr tau l_e_refis)) (appr g (appr f (appr (abst l+2 (abst l+1 nsigma x\ tau) y\ (appr (appr s y) (appr (appr s f) (appr tau l_e_is)))) (appr (abst l+1 nsigma x\ tau) l_e_isp)))))))))))))
.

g+line2 l_e_fisi 6742
       (abst l+1 (sort k+set) nsigma\ (abst l+1 (sort k+set) tau\ (abst l+1 (abst l+1 nsigma x\ tau) f\ (abst l+1 (abst l+1 nsigma x\ tau) g\ (abst l+1 (abst l+1 nsigma x\ (appr (appr x g) (appr (appr x f) (appr tau l_e_is)))) i\ (appr g (appr f (appr (abst l+1 nsigma x\ tau) l_e_is))))))))
.

g+line2 l_e_fis_th1 6741
       (abst l+2 (sort k+set) nsigma\ (abst l+2 (sort k+set) tau\ (abst l+2 (abst l+1 nsigma x\ tau) f\ (abst l+2 (abst l+1 nsigma x\ tau) g\ (abst l+2 (appr g (appr f (appr (abst l+1 nsigma x\ tau) l_e_is))) i\ (abst l+2 nsigma s\ (abst l+2 nsigma t\ (abst l+2 (appr t (appr s (appr nsigma l_e_is))) j\ (cast (appr (appr t g) (appr (appr s f) (appr tau l_e_is))) (appr (appr t (appr i (appr g (appr f (appr tau (appr nsigma l_e_fise)))))) (appr (appr j (appr t (appr s (appr f (appr tau (appr nsigma l_e_isf)))))) (appr (appr t g) (appr (appr t f) (appr (appr s f) (appr tau l_e_tris)))))))))))))))
.

g+line2 l_e_ot 6740
       (abst l+1 (sort k+set) nsigma\ (abst l+1 (abst l+1 nsigma x\ (sort k+prop)) p\ (sort k+set)))
.

g+line2 l_e_in 6739
       (abst l+1 (sort k+set) nsigma\ (abst l+1 (abst l+1 nsigma x\ (sort k+prop)) p\ (abst l+1 (appr p (appr nsigma l_e_ot)) o1\ nsigma)))
.

g+line2 l_e_inp 6738
       (abst l+1 (sort k+set) nsigma\ (abst l+1 (abst l+1 nsigma x\ (sort k+prop)) p\ (abst l+1 (appr p (appr nsigma l_e_ot)) o1\ (appr (appr o1 (appr p (appr nsigma l_e_in))) p))))
.

g+line2 l_e_otax1 6737
       (abst l+1 (sort k+set) nsigma\ (abst l+1 (abst l+1 nsigma x\ (sort k+prop)) p\ (appr (abst l+2 (appr p (appr nsigma l_e_ot)) x\ (appr x (appr p (appr nsigma l_e_in)))) (appr nsigma (appr (appr p (appr nsigma l_e_ot)) l_e_injective)))))
.

g+line2 l_e_otax2 6736
       (abst l+1 (sort k+set) nsigma\ (abst l+1 (abst l+1 nsigma x\ (sort k+prop)) p\ (abst l+1 nsigma s\ (abst l+1 (appr s p) sp\ (appr s (appr (abst l+2 (appr p (appr nsigma l_e_ot)) x\ (appr x (appr p (appr nsigma l_e_in)))) (appr nsigma (appr (appr p (appr nsigma l_e_ot)) l_e_image))))))))
.

g+line2 l_e_isini 6735
       (abst l+2 (sort k+set) nsigma\ (abst l+2 (abst l+1 nsigma x\ (sort k+prop)) p\ (abst l+2 (appr p (appr nsigma l_e_ot)) o1\ (abst l+2 (appr p (appr nsigma l_e_ot)) o2\ (abst l+2 (appr o2 (appr o1 (appr (appr p (appr nsigma l_e_ot)) l_e_is))) i\ (cast (appr (appr o2 (appr p (appr nsigma l_e_in))) (appr (appr o1 (appr p (appr nsigma l_e_in))) (appr nsigma l_e_is))) (appr i (appr o2 (appr o1 (appr (abst l+2 (appr p (appr nsigma l_e_ot)) x\ (appr x (appr p (appr nsigma l_e_in)))) (appr nsigma (appr (appr p (appr nsigma l_e_ot)) l_e_isf))))))))))))
.

g+line2 l_e_isine 6734
       (abst l+2 (sort k+set) nsigma\ (abst l+2 (abst l+1 nsigma x\ (sort k+prop)) p\ (abst l+2 (appr p (appr nsigma l_e_ot)) o1\ (abst l+2 (appr p (appr nsigma l_e_ot)) o2\ (abst l+2 (appr (appr o2 (appr p (appr nsigma l_e_in))) (appr (appr o1 (appr p (appr nsigma l_e_in))) (appr nsigma l_e_is))) i\ (cast (appr o2 (appr o1 (appr (appr p (appr nsigma l_e_ot)) l_e_is))) (appr i (appr o2 (appr o1 (appr (appr p (appr nsigma l_e_otax1)) (appr (abst l+2 (appr p (appr nsigma l_e_ot)) x\ (appr x (appr p (appr nsigma l_e_in)))) (appr nsigma (appr (appr p (appr nsigma l_e_ot)) l_e_isfe)))))))))))))
.

g+line2 l_e_out 6733
       (abst l+2 (sort k+set) nsigma\ (abst l+2 (abst l+1 nsigma x\ (sort k+prop)) p\ (abst l+2 nsigma s\ (abst l+2 (appr s p) sp\ (cast (appr p (appr nsigma l_e_ot)) (appr (appr sp (appr s (appr p (appr nsigma l_e_otax2)))) (appr s (appr (appr p (appr nsigma l_e_otax1)) (appr (abst l+2 (appr p (appr nsigma l_e_ot)) x\ (appr x (appr p (appr nsigma l_e_in)))) (appr nsigma (appr (appr p (appr nsigma l_e_ot)) l_e_soft)))))))))))
.

g+line2 l_e_isouti 6732
       (abst l+2 (sort k+set) nsigma\ (abst l+2 (abst l+1 nsigma x\ (sort k+prop)) p\ (abst l+2 nsigma s\ (abst l+2 (appr s p) sp\ (abst l+2 nsigma t\ (abst l+2 (appr t p) tp\ (abst l+2 (appr t (appr s (appr nsigma l_e_is))) i\ (cast (appr (appr tp (appr t (appr p (appr nsigma l_e_out)))) (appr (appr sp (appr s (appr p (appr nsigma l_e_out)))) (appr (appr p (appr nsigma l_e_ot)) l_e_is))) (appr i (appr (appr tp (appr t (appr p (appr nsigma l_e_otax2)))) (appr t (appr (appr sp (appr s (appr p (appr nsigma l_e_otax2)))) (appr s (appr (appr p (appr nsigma l_e_otax1)) (appr (abst l+2 (appr p (appr nsigma l_e_ot)) x\ (appr x (appr p (appr nsigma l_e_in)))) (appr nsigma (appr (appr p (appr nsigma l_e_ot)) l_e_isinv)))))))))))))))))
.

g+line2 l_e_isoute 6731
       (abst l+2 (sort k+set) nsigma\ (abst l+2 (abst l+1 nsigma x\ (sort k+prop)) p\ (abst l+2 nsigma s\ (abst l+2 (appr s p) sp\ (abst l+2 nsigma t\ (abst l+2 (appr t p) tp\ (abst l+2 (appr (appr tp (appr t (appr p (appr nsigma l_e_out)))) (appr (appr sp (appr s (appr p (appr nsigma l_e_out)))) (appr (appr p (appr nsigma l_e_ot)) l_e_is))) i\ (cast (appr t (appr s (appr nsigma l_e_is))) (appr i (appr (appr tp (appr t (appr p (appr nsigma l_e_otax2)))) (appr t (appr (appr sp (appr s (appr p (appr nsigma l_e_otax2)))) (appr s (appr (appr p (appr nsigma l_e_otax1)) (appr (abst l+2 (appr p (appr nsigma l_e_ot)) x\ (appr x (appr p (appr nsigma l_e_in)))) (appr nsigma (appr (appr p (appr nsigma l_e_ot)) l_e_isinve)))))))))))))))))
.

g+line2 l_e_isoutin 6730
       (abst l+2 (sort k+set) nsigma\ (abst l+2 (abst l+1 nsigma x\ (sort k+prop)) p\ (abst l+2 (appr p (appr nsigma l_e_ot)) o1\ (cast (appr (appr (appr o1 (appr p (appr nsigma l_e_inp))) (appr (appr o1 (appr p (appr nsigma l_e_in))) (appr p (appr nsigma l_e_out)))) (appr o1 (appr (appr p (appr nsigma l_e_ot)) l_e_is))) (appr (appr (appr (appr o1 (appr p (appr nsigma l_e_in))) (appr nsigma l_e_refis)) (appr (appr (appr o1 (appr p (appr nsigma l_e_inp))) (appr (appr o1 (appr p (appr nsigma l_e_in))) (appr p (appr nsigma l_e_otax2)))) (appr (appr o1 (appr p (appr nsigma l_e_in))) (appr (appr o1 (appr (abst l+2 (appr p (appr nsigma l_e_ot)) x\ (appr x (appr p (appr nsigma l_e_in)))) (appr nsigma (appr (appr p (appr nsigma l_e_ot)) l_e_imagei)))) (appr (appr o1 (appr p (appr nsigma l_e_in))) (appr (appr p (appr nsigma l_e_otax1)) (appr (abst l+2 (appr p (appr nsigma l_e_ot)) x\ (appr x (appr p (appr nsigma l_e_in)))) (appr nsigma (appr (appr p (appr nsigma l_e_ot)) l_e_isinv))))))))) (appr (appr o1 (appr (appr p (appr nsigma l_e_otax1)) (appr (abst l+2 (appr p (appr nsigma l_e_ot)) x\ (appr x (appr p (appr nsigma l_e_in)))) (appr nsigma (appr (appr p (appr nsigma l_e_ot)) l_e_isst1))))) (appr (appr (appr o1 (appr p (appr nsigma l_e_inp))) (appr (appr o1 (appr p (appr nsigma l_e_in))) (appr p (appr nsigma l_e_out)))) (appr (appr (appr o1 (appr (abst l+2 (appr p (appr nsigma l_e_ot)) x\ (appr x (appr p (appr nsigma l_e_in)))) (appr nsigma (appr (appr p (appr nsigma l_e_ot)) l_e_imagei)))) (appr (appr o1 (appr p (appr nsigma l_e_in))) (appr (appr p (appr nsigma l_e_otax1)) (appr (abst l+2 (appr p (appr nsigma l_e_ot)) x\ (appr x (appr p (appr nsigma l_e_in)))) (appr nsigma (appr (appr p (appr nsigma l_e_ot)) l_e_soft)))))) (appr o1 (appr (appr p (appr nsigma l_e_ot)) l_e_tris))))))))))
.

g+line2 l_e_isinout 6729
       (abst l+2 (sort k+set) nsigma\ (abst l+2 (abst l+1 nsigma x\ (sort k+prop)) p\ (abst l+2 nsigma s\ (abst l+2 (appr s p) sp\ (cast (appr (appr (appr sp (appr s (appr p (appr nsigma l_e_out)))) (appr p (appr nsigma l_e_in))) (appr s (appr nsigma l_e_is))) (appr (appr sp (appr s (appr p (appr nsigma l_e_otax2)))) (appr s (appr (appr p (appr nsigma l_e_otax1)) (appr (abst l+2 (appr p (appr nsigma l_e_ot)) x\ (appr x (appr p (appr nsigma l_e_in)))) (appr nsigma (appr (appr p (appr nsigma l_e_ot)) l_e_ists1)))))))))))
.

g+line2 l_e_pairtype 6728
       (abst l+1 (sort k+set) nsigma\ (abst l+1 (sort k+set) tau\ (sort k+set)))
.

g+line2 l_e_pair 6727
       (abst l+1 (sort k+set) nsigma\ (abst l+1 (sort k+set) tau\ (abst l+1 nsigma s\ (abst l+1 tau t\ (appr tau (appr nsigma l_e_pairtype))))))
.

g+line2 l_e_first 6726
       (abst l+1 (sort k+set) nsigma\ (abst l+1 (sort k+set) tau\ (abst l+1 (appr tau (appr nsigma l_e_pairtype)) p1\ nsigma)))
.

g+line2 l_e_second 6725
       (abst l+1 (sort k+set) nsigma\ (abst l+1 (sort k+set) tau\ (abst l+1 (appr tau (appr nsigma l_e_pairtype)) p1\ tau)))
.

g+line2 l_e_pairis1 6724
       (abst l+1 (sort k+set) nsigma\ (abst l+1 (sort k+set) tau\ (abst l+1 (appr tau (appr nsigma l_e_pairtype)) p1\ (appr p1 (appr (appr (appr p1 (appr tau (appr nsigma l_e_second))) (appr (appr p1 (appr tau (appr nsigma l_e_first))) (appr tau (appr nsigma l_e_pair)))) (appr (appr tau (appr nsigma l_e_pairtype)) l_e_is))))))
.

g+line2 l_e_pairis2 6723
       (abst l+2 (sort k+set) nsigma\ (abst l+2 (sort k+set) tau\ (abst l+2 (appr tau (appr nsigma l_e_pairtype)) p1\ (cast (appr (appr (appr p1 (appr tau (appr nsigma l_e_second))) (appr (appr p1 (appr tau (appr nsigma l_e_first))) (appr tau (appr nsigma l_e_pair)))) (appr p1 (appr (appr tau (appr nsigma l_e_pairtype)) l_e_is))) (appr (appr p1 (appr tau (appr nsigma l_e_pairis1))) (appr p1 (appr (appr (appr p1 (appr tau (appr nsigma l_e_second))) (appr (appr p1 (appr tau (appr nsigma l_e_first))) (appr tau (appr nsigma l_e_pair)))) (appr (appr tau (appr nsigma l_e_pairtype)) l_e_symis))))))))
.

g+line2 l_e_firstis1 6722
       (abst l+1 (sort k+set) nsigma\ (abst l+1 (sort k+set) tau\ (abst l+1 nsigma s\ (abst l+1 tau t\ (appr s (appr (appr (appr t (appr s (appr tau (appr nsigma l_e_pair)))) (appr tau (appr nsigma l_e_first))) (appr nsigma l_e_is)))))))
.

g+line2 l_e_firstis2 6721
       (abst l+2 (sort k+set) nsigma\ (abst l+2 (sort k+set) tau\ (abst l+2 nsigma s\ (abst l+2 tau t\ (cast (appr (appr (appr t (appr s (appr tau (appr nsigma l_e_pair)))) (appr tau (appr nsigma l_e_first))) (appr s (appr nsigma l_e_is))) (appr (appr t (appr s (appr tau (appr nsigma l_e_firstis1)))) (appr s (appr (appr (appr t (appr s (appr tau (appr nsigma l_e_pair)))) (appr tau (appr nsigma l_e_first))) (appr nsigma l_e_symis)))))))))
.

g+line2 l_e_secondis1 6720
       (abst l+1 (sort k+set) nsigma\ (abst l+1 (sort k+set) tau\ (abst l+1 nsigma s\ (abst l+1 tau t\ (appr t (appr (appr (appr t (appr s (appr tau (appr nsigma l_e_pair)))) (appr tau (appr nsigma l_e_second))) (appr tau l_e_is)))))))
.

g+line2 l_e_secondis2 6719
       (abst l+2 (sort k+set) nsigma\ (abst l+2 (sort k+set) tau\ (abst l+2 nsigma s\ (abst l+2 tau t\ (cast (appr (appr (appr t (appr s (appr tau (appr nsigma l_e_pair)))) (appr tau (appr nsigma l_e_second))) (appr t (appr tau l_e_is))) (appr (appr t (appr s (appr tau (appr nsigma l_e_secondis1)))) (appr t (appr (appr (appr t (appr s (appr tau (appr nsigma l_e_pair)))) (appr tau (appr nsigma l_e_second))) (appr tau l_e_symis)))))))))
.

g+line2 l_e_ite_prop1 6718
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 ksi z\ (cast (sort k+prop) (appr (appr (appr y (appr z (appr ksi l_e_is))) (appr (appr a l_not) l_imp)) (appr (appr (appr x (appr z (appr ksi l_e_is))) (appr a l_imp)) l_and))))))))
.

g+line2 l_e_ite_t1 6717
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 a a1\ (abst l+2 ksi x1\ (abst l+2 ksi y1\ (abst l+2 (appr x1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) px1\ (abst l+2 (appr y1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) py1\ (cast (appr (appr x (appr x1 (appr ksi l_e_is))) (appr a l_imp)) (appr px1 (appr (appr (appr y (appr x1 (appr ksi l_e_is))) (appr (appr a l_not) l_imp)) (appr (appr (appr x (appr x1 (appr ksi l_e_is))) (appr a l_imp)) l_ande1)))))))))))))
.

g+line2 l_e_ite_t2 6716
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 a a1\ (abst l+2 ksi x1\ (abst l+2 ksi y1\ (abst l+2 (appr x1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) px1\ (abst l+2 (appr y1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) py1\ (cast (appr x (appr x1 (appr ksi l_e_is))) (appr (appr py1 (appr px1 (appr y1 (appr x1 (appr a1 (appr y (appr x (appr ksi (appr a l_e_ite_t1))))))))) (appr a1 (appr (appr x (appr x1 (appr ksi l_e_is))) (appr a l_mp))))))))))))))
.

g+line2 l_e_ite_t3 6715
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 a a1\ (abst l+2 ksi x1\ (abst l+2 ksi y1\ (abst l+2 (appr x1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) px1\ (abst l+2 (appr y1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) py1\ (cast (appr x (appr y1 (appr ksi l_e_is))) (appr px1 (appr py1 (appr x1 (appr y1 (appr a1 (appr y (appr x (appr ksi (appr a l_e_ite_t2)))))))))))))))))))
.

g+line2 l_e_ite_t4 6714
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 a a1\ (abst l+2 ksi x1\ (abst l+2 ksi y1\ (abst l+2 (appr x1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) px1\ (abst l+2 (appr y1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) py1\ (cast (appr y1 (appr x1 (appr ksi l_e_is))) (appr (appr py1 (appr px1 (appr y1 (appr x1 (appr a1 (appr y (appr x (appr ksi (appr a l_e_ite_t3))))))))) (appr (appr py1 (appr px1 (appr y1 (appr x1 (appr a1 (appr y (appr x (appr ksi (appr a l_e_ite_t2))))))))) (appr x (appr y1 (appr x1 (appr ksi l_e_tris2))))))))))))))))
.

g+line2 l_e_ite_t5 6713
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 a a1\ (cast (appr (abst l+2 ksi t\ (appr t (appr y (appr x (appr ksi (appr a l_e_ite_prop1)))))) (appr ksi l_e_amone)) (abst l+2 ksi s\ (abst l+2 ksi t\ (abst l+2 (appr s (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) ps\ (abst l+2 (appr t (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) pt\ (appr pt (appr ps (appr t (appr s (appr a1 (appr y (appr x (appr ksi (appr a l_e_ite_t4)))))))))))))))))))
.

g+line2 l_e_ite_t6 6712
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 a a1\ (cast (appr (appr x (appr x (appr ksi l_e_is))) (appr a l_imp)) (abst l+2 a x1\ (appr x (appr ksi l_e_refis)))))))))
.

g+line2 l_e_ite_t7 6711
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 a a1\ (cast (appr (appr y (appr x (appr ksi l_e_is))) (appr (appr a l_not) l_imp)) (appr (appr a1 (appr a l_weli)) (appr (appr y (appr x (appr ksi l_e_is))) (appr (appr a l_not) l_imp_th2)))))))))
.

g+line2 l_e_ite_t8 6710
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 a a1\ (cast (appr x (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) (appr (appr a1 (appr y (appr x (appr ksi (appr a l_e_ite_t7))))) (appr (appr a1 (appr y (appr x (appr ksi (appr a l_e_ite_t6))))) (appr (appr (appr y (appr x (appr ksi l_e_is))) (appr (appr a l_not) l_imp)) (appr (appr (appr x (appr x (appr ksi l_e_is))) (appr a l_imp)) l_andi))))))))))
.

g+line2 l_e_ite_t9 6709
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 a a1\ (cast (appr (abst l+2 ksi t\ (appr t (appr y (appr x (appr ksi (appr a l_e_ite_prop1)))))) (appr ksi l_some)) (appr (appr a1 (appr y (appr x (appr ksi (appr a l_e_ite_t8))))) (appr x (appr (abst l+2 ksi t\ (appr t (appr y (appr x (appr ksi (appr a l_e_ite_prop1)))))) (appr ksi l_somei))))))))))
.

g+line2 l_e_ite_t10 6708
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 a a1\ (cast (appr (abst l+2 ksi t\ (appr t (appr y (appr x (appr ksi (appr a l_e_ite_prop1)))))) (appr ksi l_e_one)) (appr (appr a1 (appr y (appr x (appr ksi (appr a l_e_ite_t9))))) (appr (appr a1 (appr y (appr x (appr ksi (appr a l_e_ite_t5))))) (appr (abst l+2 ksi t\ (appr t (appr y (appr x (appr ksi (appr a l_e_ite_prop1)))))) (appr ksi l_e_onei))))))))))
.

g+line2 l_e_ite_t11 6707
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 (appr a l_not) n\ (abst l+2 ksi x1\ (abst l+2 ksi y1\ (abst l+2 (appr x1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) px1\ (abst l+2 (appr y1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) py1\ (cast (appr (appr y (appr x1 (appr ksi l_e_is))) (appr (appr a l_not) l_imp)) (appr px1 (appr (appr (appr y (appr x1 (appr ksi l_e_is))) (appr (appr a l_not) l_imp)) (appr (appr (appr x (appr x1 (appr ksi l_e_is))) (appr a l_imp)) l_ande2)))))))))))))
.

g+line2 l_e_ite_t12 6706
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 (appr a l_not) n\ (abst l+2 ksi x1\ (abst l+2 ksi y1\ (abst l+2 (appr x1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) px1\ (abst l+2 (appr y1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) py1\ (cast (appr y (appr x1 (appr ksi l_e_is))) (appr (appr py1 (appr px1 (appr y1 (appr x1 (appr n (appr y (appr x (appr ksi (appr a l_e_ite_t11))))))))) (appr n (appr (appr y (appr x1 (appr ksi l_e_is))) (appr (appr a l_not) l_mp))))))))))))))
.

g+line2 l_e_ite_t13 6705
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 (appr a l_not) n\ (abst l+2 ksi x1\ (abst l+2 ksi y1\ (abst l+2 (appr x1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) px1\ (abst l+2 (appr y1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) py1\ (cast (appr y (appr y1 (appr ksi l_e_is))) (appr px1 (appr py1 (appr x1 (appr y1 (appr n (appr y (appr x (appr ksi (appr a l_e_ite_t12)))))))))))))))))))
.

g+line2 l_e_ite_t14 6704
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 (appr a l_not) n\ (abst l+2 ksi x1\ (abst l+2 ksi y1\ (abst l+2 (appr x1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) px1\ (abst l+2 (appr y1 (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) py1\ (cast (appr y1 (appr x1 (appr ksi l_e_is))) (appr (appr py1 (appr px1 (appr y1 (appr x1 (appr n (appr y (appr x (appr ksi (appr a l_e_ite_t13))))))))) (appr (appr py1 (appr px1 (appr y1 (appr x1 (appr n (appr y (appr x (appr ksi (appr a l_e_ite_t12))))))))) (appr y (appr y1 (appr x1 (appr ksi l_e_tris2))))))))))))))))
.

g+line2 l_e_ite_t15 6703
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 (appr a l_not) n\ (cast (appr (abst l+2 ksi t\ (appr t (appr y (appr x (appr ksi (appr a l_e_ite_prop1)))))) (appr ksi l_e_amone)) (abst l+2 ksi s\ (abst l+2 ksi t\ (abst l+2 (appr s (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) ps\ (abst l+2 (appr t (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) pt\ (appr pt (appr ps (appr t (appr s (appr n (appr y (appr x (appr ksi (appr a l_e_ite_t14)))))))))))))))))))
.

g+line2 l_e_ite_t16 6702
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 (appr a l_not) n\ (cast (appr (appr y (appr y (appr ksi l_e_is))) (appr (appr a l_not) l_imp)) (abst l+2 (appr a l_not) x1\ (appr y (appr ksi l_e_refis)))))))))
.

g+line2 l_e_ite_t17 6701
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 (appr a l_not) n\ (cast (appr (appr x (appr y (appr ksi l_e_is))) (appr a l_imp)) (appr n (appr (appr x (appr y (appr ksi l_e_is))) (appr a l_imp_th2)))))))))
.

g+line2 l_e_ite_t18 6700
       (abst l+2 (sort k+prop) a\ (abst l+2 (sort k+set) ksi\ (abst l+2 ksi x\ (abst l+2 ksi y\ (abst l+2 (appr a l_not) n\ (cast (appr y (appr y (appr x (appr ksi (appr a l_e_ite_prop1))))) (appr (appr n (appr y (appr x (appr ksi (appr a l_e_ite_t16))))) (appr (appr n (appr y (appr x (appr ksi (appr a l_e_ite_t17))))) (appr (appr (appr y (appr y (appr ksi l_e_is))) (appr (appr a l_not) l_imp)) (appr (appr (appr x (appr y (appr ksi l_e_is))) (appr a l_imp)) l_andi))))))))))
.
