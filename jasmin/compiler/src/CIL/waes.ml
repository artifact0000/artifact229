open BinNums
open Datatypes
open Seq
open Ssralg
open Ssrnat
open Word0
open Word
open Wsize

(** val coq_Sbox : GRing.ComRing.sort -> GRing.ComRing.sort **)

let coq_Sbox v1 =
  wrepr U8
    (match toword (S (wsize_size_minus_1 U8)) (Obj.magic v1) with
     | Z0 -> Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
     | Zpos p ->
       (match p with
        | Coq_xI p0 ->
          (match p0 with
           | Coq_xI p1 ->
             (match p1 with
              | Coq_xI p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xO (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                              (Coq_xO (Coq_xI Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                           Coq_xH)))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                        (Coq_xI Coq_xH))))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                              (Coq_xI (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                              (Coq_xO Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                           (Coq_xO Coq_xH))))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                           (Coq_xI Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                        (Coq_xI Coq_xH))))))))
                 | Coq_xH ->
                   Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                     Coq_xH)))))))
              | Coq_xO p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI Coq_xH)))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                              Coq_xH))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                              Coq_xH))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                           (Coq_xI Coq_xH))))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                              (Coq_xI Coq_xH)))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                           (Coq_xI Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                        (Coq_xO Coq_xH))))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                              (Coq_xI (Coq_xI Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                           (Coq_xI Coq_xH))))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO Coq_xH)))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                              (Coq_xI (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                           Coq_xH))))))
                    | Coq_xH ->
                      Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                        Coq_xH)))))))
                 | Coq_xH ->
                   Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
              | Coq_xH ->
                Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                  Coq_xH))))))))
           | Coq_xO p1 ->
             (match p1 with
              | Coq_xI p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                              (Coq_xI (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                              (Coq_xO Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                           Coq_xH))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                              Coq_xH))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                              (Coq_xI (Coq_xI Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                           (Coq_xI Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                        (Coq_xO Coq_xH))))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH -> Zpos (Coq_xI Coq_xH)
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                              (Coq_xI (Coq_xI Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                           (Coq_xO Coq_xH))))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH -> Zpos (Coq_xO (Coq_xI Coq_xH))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                              (Coq_xO Coq_xH)))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                              (Coq_xI Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                           Coq_xH))))))
                    | Coq_xH ->
                      Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                        Coq_xH)))))))
                 | Coq_xH ->
                   Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                     (Coq_xI Coq_xH))))))))
              | Coq_xO p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                              (Coq_xO (Coq_xI Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                              (Coq_xI (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                              Coq_xH))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                           (Coq_xO Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                        (Coq_xI Coq_xH))))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xO (Coq_xI Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                           (Coq_xI Coq_xH))))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                              (Coq_xI (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                           (Coq_xI Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                        (Coq_xO Coq_xH))))))))
                 | Coq_xH -> Zpos Coq_xH)
              | Coq_xH ->
                Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                  Coq_xH)))))))
           | Coq_xH ->
             Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))))
        | Coq_xO p0 ->
          (match p0 with
           | Coq_xI p1 ->
             (match p1 with
              | Coq_xI p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xI (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO Coq_xH)))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                              (Coq_xO Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                           (Coq_xO Coq_xH))))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                              Coq_xH))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                           Coq_xH))))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                        Coq_xH)))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                              Coq_xH))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xH -> Zpos (Coq_xI (Coq_xO Coq_xH)))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                              Coq_xH))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                              (Coq_xO Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                           (Coq_xI Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                        Coq_xH)))))))
                 | Coq_xH ->
                   Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                     (Coq_xO Coq_xH))))))))
              | Coq_xO p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                              (Coq_xO (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                           (Coq_xO Coq_xH))))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH -> Zpos (Coq_xO Coq_xH))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                              (Coq_xO (Coq_xI Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                           (Coq_xI Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                        (Coq_xO Coq_xH))))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                              (Coq_xO Coq_xH)))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH -> Z0)
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                           Coq_xH))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                              Coq_xH))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                           (Coq_xO Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                        (Coq_xI Coq_xH))))))))
                 | Coq_xH ->
                   Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                     Coq_xH)))))))
              | Coq_xH ->
                Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                  Coq_xH)))))))
           | Coq_xO p1 ->
             (match p1 with
              | Coq_xI p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                              (Coq_xO Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                           (Coq_xI Coq_xH))))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xO Coq_xH)))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                              Coq_xH))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                           Coq_xH)))))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                        (Coq_xO Coq_xH))))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                              Coq_xH))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                              (Coq_xO Coq_xH)))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                           Coq_xH))))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                        (Coq_xI Coq_xH))))))))
                 | Coq_xH ->
                   Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                     (Coq_xI Coq_xH))))))))
              | Coq_xO p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                              (Coq_xI Coq_xH)))))))
                       | Coq_xH -> Zpos (Coq_xI (Coq_xI Coq_xH)))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                              (Coq_xO Coq_xH)))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xO Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                           Coq_xH))))))
                    | Coq_xH ->
                      Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                        (Coq_xO Coq_xH))))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xO Coq_xH)))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xO Coq_xH)))))))
                       | Coq_xH -> Zpos (Coq_xO (Coq_xO Coq_xH)))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xO (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH -> Zpos (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                           (Coq_xO Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                        (Coq_xI Coq_xH))))))))
                 | Coq_xH ->
                   Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
              | Coq_xH ->
                Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                  Coq_xH))))))))
           | Coq_xH ->
             Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))))
        | Coq_xH ->
          Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))))
     | Zneg _ -> Z0)

(** val coq_InvSbox : GRing.ComRing.sort -> GRing.ComRing.sort **)

let coq_InvSbox v1 =
  wrepr U8
    (match toword (S (wsize_size_minus_1 U8)) (Obj.magic v1) with
     | Z0 -> Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
     | Zpos p ->
       (match p with
        | Coq_xI p0 ->
          (match p0 with
           | Coq_xI p1 ->
             (match p1 with
              | Coq_xI p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                              (Coq_xI Coq_xH)))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                           Coq_xH))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
                             | _ -> Z0)
                          | Coq_xH -> Zpos (Coq_xO (Coq_xI Coq_xH)))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                           Coq_xH)))))))
                    | Coq_xH ->
                      Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                        (Coq_xI Coq_xH))))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xH -> Zpos (Coq_xO Coq_xH))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                              (Coq_xO (Coq_xI Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                           (Coq_xO Coq_xH))))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH -> Zpos (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                           Coq_xH))))))
                    | Coq_xH ->
                      Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                        (Coq_xO Coq_xH))))))))
                 | Coq_xH ->
                   Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                     (Coq_xI Coq_xH))))))))
              | Coq_xO p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH -> Zpos (Coq_xI Coq_xH))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                              (Coq_xO Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                           Coq_xH)))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
                             | _ -> Z0)
                          | Coq_xH -> Zpos (Coq_xI (Coq_xO Coq_xH)))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                              (Coq_xO (Coq_xI Coq_xH))))))))
                       | Coq_xH -> Zpos (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                        Coq_xH)))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xO Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                           Coq_xH)))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH -> Z0)
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                              (Coq_xI Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                           Coq_xH))))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                        (Coq_xO Coq_xH))))))))
                 | Coq_xH ->
                   Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                     (Coq_xO Coq_xH))))))))
              | Coq_xH ->
                Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
           | Coq_xO p1 ->
             (match p1 with
              | Coq_xI p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                           (Coq_xO Coq_xH))))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                              (Coq_xI Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                           (Coq_xI Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                        (Coq_xI Coq_xH))))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                              Coq_xH))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                              (Coq_xI (Coq_xI Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                           (Coq_xI Coq_xH))))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH -> Zpos (Coq_xI (Coq_xI Coq_xH))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                              (Coq_xI Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                           (Coq_xI Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
                 | Coq_xH ->
                   Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                     (Coq_xI Coq_xH))))))))
              | Coq_xO p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                           Coq_xH)))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                              (Coq_xI (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                           Coq_xH)))))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                        (Coq_xO Coq_xH))))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                              Coq_xH))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xI Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                           Coq_xH))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                              (Coq_xO (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                              (Coq_xI (Coq_xI Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                           Coq_xH)))))))
                    | Coq_xH ->
                      Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                        (Coq_xI Coq_xH))))))))
                 | Coq_xH ->
                   Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                     Coq_xH)))))))
              | Coq_xH ->
                Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
           | Coq_xH ->
             Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
               Coq_xH))))))))
        | Coq_xO p0 ->
          (match p0 with
           | Coq_xI p1 ->
             (match p1 with
              | Coq_xI p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                           (Coq_xI Coq_xH))))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                              (Coq_xO Coq_xH)))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                           (Coq_xI Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                        (Coq_xI Coq_xH))))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH -> Zpos (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                           Coq_xH))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xO (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                           Coq_xH))))))
                    | Coq_xH ->
                      Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                        (Coq_xI Coq_xH))))))))
                 | Coq_xH ->
                   Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                     (Coq_xI Coq_xH))))))))
              | Coq_xO p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                              (Coq_xO Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                           (Coq_xO Coq_xH))))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                              (Coq_xO Coq_xH)))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                              (Coq_xO Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                           (Coq_xO Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                        Coq_xH)))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH -> Zpos (Coq_xO (Coq_xO Coq_xH))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                              (Coq_xO Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                           (Coq_xO Coq_xH))))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                              (Coq_xI (Coq_xI Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                           (Coq_xO Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
                 | Coq_xH ->
                   Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                     (Coq_xO Coq_xH))))))))
              | Coq_xH ->
                Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                  Coq_xH))))))))
           | Coq_xO p1 ->
             (match p1 with
              | Coq_xI p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH -> Zpos Coq_xH)
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                           Coq_xH)))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
                              (Coq_xI (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                              (Coq_xO Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                           Coq_xH)))))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                        (Coq_xI Coq_xH))))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                              (Coq_xO (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                              (Coq_xI (Coq_xI Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                           Coq_xH))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                           (Coq_xO Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                        (Coq_xO Coq_xH))))))))
                 | Coq_xH ->
                   Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                     (Coq_xO Coq_xH))))))))
              | Coq_xO p2 ->
                (match p2 with
                 | Coq_xI p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                              (Coq_xO (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                              (Coq_xO Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                           Coq_xH)))))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
                                 (Coq_xO (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                              (Coq_xI (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
                              (Coq_xO (Coq_xI Coq_xH))))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                           (Coq_xI Coq_xH))))))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
                 | Coq_xO p3 ->
                   (match p3 with
                    | Coq_xI p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
                                 (Coq_xI (Coq_xI Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xO (Coq_xI Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xI Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
                                 (Coq_xO (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
                              (Coq_xI Coq_xH)))))))
                       | Coq_xH -> Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
                    | Coq_xO p4 ->
                      (match p4 with
                       | Coq_xI p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                                 (Coq_xI (Coq_xO Coq_xH)))))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
                                 (Coq_xO Coq_xH))))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xO (Coq_xO Coq_xH))))))))
                       | Coq_xO p5 ->
                         (match p5 with
                          | Coq_xI p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
                             | _ -> Z0)
                          | Coq_xO p6 ->
                            (match p6 with
                             | Coq_xH ->
                               Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
                                 Coq_xH)))))
                             | _ -> Z0)
                          | Coq_xH ->
                            Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
                              (Coq_xI Coq_xH)))))))
                       | Coq_xH ->
                         Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
                           Coq_xH)))))))
                    | Coq_xH ->
                      Zpos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                        Coq_xH)))))))
                 | Coq_xH ->
                   Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                     (Coq_xO Coq_xH))))))))
              | Coq_xH ->
                Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
           | Coq_xH ->
             Zpos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))))
        | Coq_xH -> Zpos (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
     | Zneg _ -> Z0)

(** val coq_SubWord : GRing.ComRing.sort -> GRing.ComRing.sort **)

let coq_SubWord v1 =
  make_vec U8 U32
    (map (Obj.magic coq_Sbox) (split_vec U32 (nat_of_wsize U8) v1))

(** val coq_InvSubWord : GRing.ComRing.sort -> GRing.ComRing.sort **)

let coq_InvSubWord v1 =
  make_vec U8 U32
    (map (Obj.magic coq_InvSbox) (split_vec U32 (nat_of_wsize U8) v1))

(** val coq_RotWord : GRing.ComRing.sort -> GRing.ComRing.sort **)

let coq_RotWord v1 =
  make_vec U8 U32
    ((Obj.magic subword (S (wsize_size_minus_1 U32))
       (muln (S O) (nat_of_wsize U8)) (nat_of_wsize U8) v1) :: ((Obj.magic
                                                                  subword (S
                                                                  (wsize_size_minus_1
                                                                    U32))
                                                                  (muln (S (S
                                                                    O))
                                                                    (nat_of_wsize
                                                                    U8))
                                                                  (nat_of_wsize
                                                                    U8) v1) :: (
    (Obj.magic subword (S (wsize_size_minus_1 U32))
      (muln (S (S (S O))) (nat_of_wsize U8)) (nat_of_wsize U8) v1) :: (
    (Obj.magic subword (S (wsize_size_minus_1 U32))
      (muln O (nat_of_wsize U8)) (nat_of_wsize U8) v1) :: []))))

(** val to_matrix :
    GRing.ComRing.sort ->
    ((((((((((((((word * word) * word) * word) * word) * word) * word) * word) * word) * word) * word) * word) * word) * word) * word) * word **)

let to_matrix s =
  let s_ = fun i j ->
    subword (nat_of_wsize U32) (muln i (nat_of_wsize U8)) (nat_of_wsize U8)
      (subword (S (wsize_size_minus_1 U128)) (muln j (nat_of_wsize U32))
        (nat_of_wsize U32) (Obj.magic s))
  in
  ((((((((((((((((s_ O O), (s_ O (S O))), (s_ O (S (S O)))),
  (s_ O (S (S (S O))))), (s_ (S O) O)), (s_ (S O) (S O))),
  (s_ (S O) (S (S O)))), (s_ (S O) (S (S (S O))))), (s_ (S (S O)) O)),
  (s_ (S (S O)) (S O))), (s_ (S (S O)) (S (S O)))),
  (s_ (S (S O)) (S (S (S O))))), (s_ (S (S (S O))) O)),
  (s_ (S (S (S O))) (S O))), (s_ (S (S (S O))) (S (S O)))),
  (s_ (S (S (S O))) (S (S (S O)))))

(** val to_state :
    (((((((((((((((GRing.ComRing.sort * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort)
    -> GRing.ComRing.sort **)

let to_state = function
| (p, s33) ->
  let (p0, s32) = p in
  let (p1, s31) = p0 in
  let (p2, s30) = p1 in
  let (p3, s23) = p2 in
  let (p4, s22) = p3 in
  let (p5, s21) = p4 in
  let (p6, s20) = p5 in
  let (p7, s13) = p6 in
  let (p8, s12) = p7 in
  let (p9, s11) = p8 in
  let (p10, s10) = p9 in
  let (p11, s03) = p10 in
  let (p12, s02) = p11 in
  let (s00, s01) = p12 in
  let c0 = make_vec U8 U32 (s00 :: (s10 :: (s20 :: (s30 :: [])))) in
  let c1 = make_vec U8 U32 (s01 :: (s11 :: (s21 :: (s31 :: [])))) in
  let c2 = make_vec U8 U32 (s02 :: (s12 :: (s22 :: (s32 :: [])))) in
  let c3 = make_vec U8 U32 (s03 :: (s13 :: (s23 :: (s33 :: [])))) in
  make_vec U32 U128 (c0 :: (c1 :: (c2 :: (c3 :: []))))

(** val coq_SubBytes : GRing.ComRing.sort -> GRing.ComRing.sort **)

let coq_SubBytes s =
  make_vec U32 U128
    (map (Obj.magic coq_SubWord) (split_vec U128 (nat_of_wsize U32) s))

(** val coq_InvSubBytes : GRing.ComRing.sort -> GRing.ComRing.sort **)

let coq_InvSubBytes s =
  make_vec U32 U128
    (map (Obj.magic coq_InvSubWord) (split_vec U128 (nat_of_wsize U32) s))

(** val coq_ShiftRows : GRing.ComRing.sort -> GRing.ComRing.sort **)

let coq_ShiftRows s =
  let (p, s33) = to_matrix s in
  let (p0, s32) = p in
  let (p1, s31) = p0 in
  let (p2, s30) = p1 in
  let (p3, s23) = p2 in
  let (p4, s22) = p3 in
  let (p5, s21) = p4 in
  let (p6, s20) = p5 in
  let (p7, s13) = p6 in
  let (p8, s12) = p7 in
  let (p9, s11) = p8 in
  let (p10, s10) = p9 in
  let (p11, s03) = p10 in
  let (p12, s02) = p11 in
  let (s00, s01) = p12 in
  to_state ((((((((((((((((Obj.magic s00), (Obj.magic s01)),
    (Obj.magic s02)), (Obj.magic s03)), (Obj.magic s11)), (Obj.magic s12)),
    (Obj.magic s13)), (Obj.magic s10)), (Obj.magic s22)), (Obj.magic s23)),
    (Obj.magic s20)), (Obj.magic s21)), (Obj.magic s33)), (Obj.magic s30)),
    (Obj.magic s31)), (Obj.magic s32))

(** val coq_InvShiftRows : GRing.ComRing.sort -> GRing.ComRing.sort **)

let coq_InvShiftRows s =
  let (p, s32) = to_matrix s in
  let (p0, s31) = p in
  let (p1, s30) = p0 in
  let (p2, s33) = p1 in
  let (p3, s21) = p2 in
  let (p4, s20) = p3 in
  let (p5, s23) = p4 in
  let (p6, s22) = p5 in
  let (p7, s10) = p6 in
  let (p8, s13) = p7 in
  let (p9, s12) = p8 in
  let (p10, s11) = p9 in
  let (p11, s03) = p10 in
  let (p12, s02) = p11 in
  let (s00, s01) = p12 in
  to_state ((((((((((((((((Obj.magic s00), (Obj.magic s01)),
    (Obj.magic s02)), (Obj.magic s03)), (Obj.magic s10)), (Obj.magic s11)),
    (Obj.magic s12)), (Obj.magic s13)), (Obj.magic s20)), (Obj.magic s21)),
    (Obj.magic s22)), (Obj.magic s23)), (Obj.magic s30)), (Obj.magic s31)),
    (Obj.magic s32)), (Obj.magic s33))

(** val coq_MixColumns : GRing.ComRing.sort -> GRing.ComRing.sort **)

let coq_MixColumns = (fun _ -> failwith "MixColumns is not implemented")

(** val coq_InvMixColumns : GRing.ComRing.sort -> GRing.ComRing.sort **)

let coq_InvMixColumns = (fun _ -> failwith "InvMixColumns not implemented")

(** val wAESDEC :
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wAESDEC state rkey =
  let state0 = coq_InvShiftRows state in
  let state1 = coq_InvSubBytes state0 in
  let state2 = coq_InvMixColumns state1 in Word0.wxor U128 state2 rkey

(** val wAESDECLAST :
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wAESDECLAST state rkey =
  let state0 = coq_InvShiftRows state in
  let state1 = coq_InvSubBytes state0 in Word0.wxor U128 state1 rkey

(** val wAESENC :
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wAESENC state rkey =
  let state0 = coq_ShiftRows state in
  let state1 = coq_SubBytes state0 in
  let state2 = coq_MixColumns state1 in Word0.wxor U128 state2 rkey

(** val wAESENCLAST :
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wAESENCLAST state rkey =
  let state0 = coq_ShiftRows state in
  let state1 = coq_SubBytes state0 in Word0.wxor U128 state1 rkey

(** val wAESKEYGENASSIST :
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wAESKEYGENASSIST v1 v2 =
  let rcon = zero_extend U32 U8 v2 in
  let x1 =
    subword (S (wsize_size_minus_1 U128)) (muln (S O) (nat_of_wsize U32))
      (nat_of_wsize U32) (Obj.magic v1)
  in
  let x3 =
    subword (S (wsize_size_minus_1 U128))
      (muln (S (S (S O))) (nat_of_wsize U32)) (nat_of_wsize U32)
      (Obj.magic v1)
  in
  let y0 = coq_SubWord (Obj.magic x1) in
  let y1 = Word0.wxor U32 (coq_RotWord (coq_SubWord (Obj.magic x1))) rcon in
  let y2 = coq_SubWord (Obj.magic x3) in
  let y3 = Word0.wxor U32 (coq_RotWord (coq_SubWord (Obj.magic x3))) rcon in
  make_vec U32 U128 (y0 :: (y1 :: (y2 :: (y3 :: []))))
