-- Source SHA-256: 4df496d4b71c2dd9a9a23307b4b324cdbdb67464e35eb696f991bc06e5d3773c
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S03b2acad
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S0430ca7c
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S078e7d20
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S109f3370
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S11c3682d
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S124d1a75
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S17759d9f
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S1b64778e
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S1e7cf533
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S208b505c
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S2350ff1c
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S25167265
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S25f5c02a
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S296108af
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S2b84589f
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S376bcb36
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S3a9f242c
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S3b72950f
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S4090edd7
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S40fa8f3f
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S4655eae1
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S48c923c1
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S4926c1f4
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S4e61b76c
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S4f28eb05
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S50193082
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S54b4417b
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S59b58d62
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S5a5b0bd5
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S62e9dae0
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S69647171
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S6aa76dac
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S6cc5a3e3
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S72392b81
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S7510344d
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S77dab681
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S7c60f425
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S7d3914ac
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S7f3fefed
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S84900580
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S877de5f3
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S8f583f42
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S93135965
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S93d0e676
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S9511d4c3
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S9589feb3
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S9ad0e971
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.S9f717b31
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sa00cb9c7
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sa3e85b88
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sa461fe12
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sa48e2d62
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sa57df17a
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sa821b93c
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sa9c18fe1
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sab87e3d4
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sac09a8d3
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sb4a69aed
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sb5ac3c34
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sb673e431
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sb751f117
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sbcd28934
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sbe534c92
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sbeb334b1
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sbefdd95b
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sc577efcd
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sc7482db2
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Scc53d7e3
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sd00ed590
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sd48e6c9f
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sd55d8b9f
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sd96a648f
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sdaed3871
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Se059a44d
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Se37df572
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Se3ca258b
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sec169b78
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sf885170c
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB.Sfe868d81

theorem FormalAB.V3.A1.claim_0239ccb0 :
    type_of% @FormalAB.Sdd81c7c9.JocelynClaims.claim_0239ccb0f1097a0e3538142061f60280042027536a82565a83970be57d81ba39 :=
  @FormalAB.Sdd81c7c9.JocelynClaims.claim_0239ccb0f1097a0e3538142061f60280042027536a82565a83970be57d81ba39

theorem FormalAB.V3.A1.claim_1f0393ec :
    type_of% @FormalAB.S9757f934.JocelynClaims.claim_1f0393ec2a6aa23d51d1d83090dcdb2879e9763b5c5666e0bde39c7fb8d44a71 :=
  @FormalAB.S9757f934.JocelynClaims.claim_1f0393ec2a6aa23d51d1d83090dcdb2879e9763b5c5666e0bde39c7fb8d44a71

theorem FormalAB.V3.A1.claim_2439f0cf :
    type_of% @FormalAB.S518618bb.JocelynClaims.claim_2439f0cf2b873792618616c393803c04f654c0214dcc578f8b298e807ddbe68b :=
  @FormalAB.S518618bb.JocelynClaims.claim_2439f0cf2b873792618616c393803c04f654c0214dcc578f8b298e807ddbe68b

theorem FormalAB.V3.A1.claim_3b4e25aa :
    type_of% @FormalAB.Sb673e431.JocelynClaims.claim_3b4e25aa7db2fd68066fb4af852f5cdf3aae12b40aec5d65bf196d127ecac621 :=
  @FormalAB.Sb673e431.JocelynClaims.claim_3b4e25aa7db2fd68066fb4af852f5cdf3aae12b40aec5d65bf196d127ecac621

theorem FormalAB.V3.A1.claim_47161fcb :
    type_of% @FormalAB.S852ada5b.JocelynClaims.claim_47161fcbf976a6fcd20031cace10f4021d598821719f081d4c6535d0c27e1618 :=
  @FormalAB.S852ada5b.JocelynClaims.claim_47161fcbf976a6fcd20031cace10f4021d598821719f081d4c6535d0c27e1618

theorem FormalAB.V3.A1.claim_485d36ff :
    type_of% @FormalAB.Sfe868d81.JocelynClaims.claim_485d36ffe22a214a121bb53fc8c57f9130d77b4f8da41eac34b05c508f152093 :=
  @FormalAB.Sfe868d81.JocelynClaims.claim_485d36ffe22a214a121bb53fc8c57f9130d77b4f8da41eac34b05c508f152093

theorem FormalAB.V3.A1.claim_527cb1df :
    type_of% @FormalAB.S6747b632.JocelynClaims.claim_527cb1df679f67f11fd73bfe9e403493f6c4372f78e8917e460bb4e16d6dcc75 :=
  @FormalAB.S6747b632.JocelynClaims.claim_527cb1df679f67f11fd73bfe9e403493f6c4372f78e8917e460bb4e16d6dcc75

theorem FormalAB.V3.A1.claim_60dcdbe9 :
    type_of% @FormalAB.Sb8604a17.JocelynClaims.claim_60dcdbe97b5a1e2b8583668b710b2c100e54010e5fbba95b57893ebfebd760ed :=
  @FormalAB.Sb8604a17.JocelynClaims.claim_60dcdbe97b5a1e2b8583668b710b2c100e54010e5fbba95b57893ebfebd760ed

theorem FormalAB.V3.A1.claim_6ee3b938 :
    type_of% @FormalAB.S61c6e1a7.JocelynClaims.claim_6ee3b93895b740106f1fc3f1ae890573d49586f2ad7de707b7e4361ec678e423 :=
  @FormalAB.S61c6e1a7.JocelynClaims.claim_6ee3b93895b740106f1fc3f1ae890573d49586f2ad7de707b7e4361ec678e423

theorem FormalAB.V3.A1.claim_70074919 :
    type_of% @FormalAB.S94d17769.JocelynClaims.claim_7007491917ec3b6c5c4a0723620dcc5cd205fa4859a5a02542b566e6ed860c0f :=
  @FormalAB.S94d17769.JocelynClaims.claim_7007491917ec3b6c5c4a0723620dcc5cd205fa4859a5a02542b566e6ed860c0f

theorem FormalAB.V3.A1.claim_7c2c78a4 :
    type_of% @FormalAB.Sbfeb2b3e.JocelynClaims.claim_7c2c78a4f5d193bc6432685b3f11f32fffd98db89209bcd624a27441e8fc7da3 :=
  @FormalAB.Sbfeb2b3e.JocelynClaims.claim_7c2c78a4f5d193bc6432685b3f11f32fffd98db89209bcd624a27441e8fc7da3

theorem FormalAB.V3.A1.claim_81ef5319 :
    type_of% @FormalAB.S27058e64.JocelynClaims.claim_81ef5319573cd818b19c90d8d6f0445c38d19596747f8261779a51aae38eefcb :=
  @FormalAB.S27058e64.JocelynClaims.claim_81ef5319573cd818b19c90d8d6f0445c38d19596747f8261779a51aae38eefcb

theorem FormalAB.V3.A1.claim_89701b0b :
    type_of% @FormalAB.Sb8e688cd.JocelynClaims.claim_89701b0bf085716cd006b540b8399bd3988a878a21011a0d669fd9ee2e0cbeb0 :=
  @FormalAB.Sb8e688cd.JocelynClaims.claim_89701b0bf085716cd006b540b8399bd3988a878a21011a0d669fd9ee2e0cbeb0

theorem FormalAB.V3.A1.claim_8c654d79 :
    type_of% @FormalAB.S4fcbc839.JocelynClaims.claim_8c654d795fd95218625287bdb4837039ac482b18e339203f6c1e251bac124482 :=
  @FormalAB.S4fcbc839.JocelynClaims.claim_8c654d795fd95218625287bdb4837039ac482b18e339203f6c1e251bac124482

theorem FormalAB.V3.A1.claim_90c70f86 :
    type_of% @FormalAB.S335fe9a1.JocelynClaims.claim_90c70f86b34ef519b1e77973542054e3b8791ed9ca4e8362cde122f3a2573b36 :=
  @FormalAB.S335fe9a1.JocelynClaims.claim_90c70f86b34ef519b1e77973542054e3b8791ed9ca4e8362cde122f3a2573b36

theorem FormalAB.V3.A1.claim_a417c464 :
    type_of% @FormalAB.S5c844e97.JocelynClaims.claim_a417c464b5ecd6f069284fb46b8cee7ca933cc2d09cd447fca9ddc0b3b0ca0a0 :=
  @FormalAB.S5c844e97.JocelynClaims.claim_a417c464b5ecd6f069284fb46b8cee7ca933cc2d09cd447fca9ddc0b3b0ca0a0

theorem FormalAB.V3.A1.claim_c5f7dc23 :
    type_of% @FormalAB.S5ecab545.JocelynClaims.claim_c5f7dc2312a89efc70bc8c31c568f8aedfe2125e39bc0d1eec0e3d7fe2bf96cd :=
  @FormalAB.S5ecab545.JocelynClaims.claim_c5f7dc2312a89efc70bc8c31c568f8aedfe2125e39bc0d1eec0e3d7fe2bf96cd

theorem FormalAB.V3.A1.claim_c6b359b5 :
    type_of% @FormalAB.S166bebe9.JocelynClaims.claim_c6b359b54a3afa460cafc6470d89a6e983a3a260f38a4709fbf098a36b184f64 :=
  @FormalAB.S166bebe9.JocelynClaims.claim_c6b359b54a3afa460cafc6470d89a6e983a3a260f38a4709fbf098a36b184f64

theorem FormalAB.V3.A1.claim_c71f1a76 :
    type_of% @FormalAB.S1fdb06b5.JocelynClaims.claim_c71f1a768cfb28c02e95bca7dd7e1140473260616bf3e851b35a285bde722dbe :=
  @FormalAB.S1fdb06b5.JocelynClaims.claim_c71f1a768cfb28c02e95bca7dd7e1140473260616bf3e851b35a285bde722dbe

theorem FormalAB.V3.A1.claim_c7bc9c01 :
    type_of% @FormalAB.Sa4f9139d.JocelynClaims.claim_c7bc9c01190325e52f64af0232d528cfb360dfdd16c7cd068dd9d4924234c0cc :=
  @FormalAB.Sa4f9139d.JocelynClaims.claim_c7bc9c01190325e52f64af0232d528cfb360dfdd16c7cd068dd9d4924234c0cc

theorem FormalAB.V3.A1.claim_c822d2a7 :
    type_of% @FormalAB.Sb47bec79.JocelynClaims.claim_c822d2a71203c95fa672436c6f2b29683c8238d884bb11fb0a4722b26213da39 :=
  @FormalAB.Sb47bec79.JocelynClaims.claim_c822d2a71203c95fa672436c6f2b29683c8238d884bb11fb0a4722b26213da39

theorem FormalAB.V3.A1.claim_ca3b5d93 :
    type_of% @FormalAB.S1b75af8c.JocelynClaims.claim_ca3b5d934d945bbf238b045d3526e130279e3edeae961500c6546aa9be13b00c :=
  @FormalAB.S1b75af8c.JocelynClaims.claim_ca3b5d934d945bbf238b045d3526e130279e3edeae961500c6546aa9be13b00c

theorem FormalAB.V3.A1.claim_cc86df2d :
    type_of% @FormalAB.S4dbaca2c.JocelynClaims.claim_cc86df2dc03c8a29b900f29c85a12e86e9e4bcd00579aa285a12a1fb4d81d610 :=
  @FormalAB.S4dbaca2c.JocelynClaims.claim_cc86df2dc03c8a29b900f29c85a12e86e9e4bcd00579aa285a12a1fb4d81d610

theorem FormalAB.V3.A1.claim_d04f7cf8 :
    type_of% @FormalAB.S93e69752.JocelynClaims.claim_d04f7cf8bd89a1c7d2f76c9392bda0f9fcec544a4632680a92742b2a6c4c51f8 :=
  @FormalAB.S93e69752.JocelynClaims.claim_d04f7cf8bd89a1c7d2f76c9392bda0f9fcec544a4632680a92742b2a6c4c51f8

theorem FormalAB.V3.A1.claim_d45d952c :
    type_of% @FormalAB.S9f3929ee.JocelynClaims.claim_d45d952cc3fbcaeb61535f99c83e1ca4aa79d169548b04160d0a27857128e379 :=
  @FormalAB.S9f3929ee.JocelynClaims.claim_d45d952cc3fbcaeb61535f99c83e1ca4aa79d169548b04160d0a27857128e379

theorem FormalAB.V3.A1.claim_d9a998ef :
    type_of% @FormalAB.S11797156.JocelynClaims.claim_d9a998efb8ded2abfc279a07f7636ea037f877a6a374821a2ff1d74e1dab8cfc :=
  @FormalAB.S11797156.JocelynClaims.claim_d9a998efb8ded2abfc279a07f7636ea037f877a6a374821a2ff1d74e1dab8cfc

theorem FormalAB.V3.A1.claim_e7555348 :
    type_of% @FormalAB.Sa50e8b97.JocelynClaims.claim_e75553485b5d2e5bd63ee65aebcf994cd97008ea56cada76cdc82729c0e76bb6 :=
  @FormalAB.Sa50e8b97.JocelynClaims.claim_e75553485b5d2e5bd63ee65aebcf994cd97008ea56cada76cdc82729c0e76bb6

theorem FormalAB.V3.A1.claim_e84c053b :
    type_of% @FormalAB.S4e2556c6.JocelynClaims.claim_e84c053b0f0a1339dbe133dcd3f17bc6c86009af8898ec98c5e726123652d8d6 :=
  @FormalAB.S4e2556c6.JocelynClaims.claim_e84c053b0f0a1339dbe133dcd3f17bc6c86009af8898ec98c5e726123652d8d6

theorem FormalAB.V3.A1.claim_e85ff2c4 :
    type_of% @FormalAB.S4211e715.JocelynClaims.claim_e85ff2c4806e84df9128836a6bfe7bd5301bc3da55d1d706cd62f16973c2a0a6 :=
  @FormalAB.S4211e715.JocelynClaims.claim_e85ff2c4806e84df9128836a6bfe7bd5301bc3da55d1d706cd62f16973c2a0a6

theorem FormalAB.V3.A1.claim_f52aedc2 :
    type_of% @FormalAB.S45a79942.JocelynClaims.claim_f52aedc206e740431409bdaca7214835f4e178b4bf127f2cf302da3b991fc005 :=
  @FormalAB.S45a79942.JocelynClaims.claim_f52aedc206e740431409bdaca7214835f4e178b4bf127f2cf302da3b991fc005

theorem FormalAB.V3.A1.claim_fd1d9a9a :
    type_of% @FormalAB.S1463b785.JocelynClaims.claim_fd1d9a9a5f6f7f3ebb97f65e48e01ad6025b2df3fd61822ba8f1818a3717b7b9 :=
  @FormalAB.S1463b785.JocelynClaims.claim_fd1d9a9a5f6f7f3ebb97f65e48e01ad6025b2df3fd61822ba8f1818a3717b7b9

theorem FormalAB.V3.A1.claim_fee060ec :
    type_of% @FormalAB.Sc2541119.JocelynClaims.claim_fee060ec8efc629cff44be0054c59b3c8de32bece45eb04411bf448f78267e84 :=
  @FormalAB.Sc2541119.JocelynClaims.claim_fee060ec8efc629cff44be0054c59b3c8de32bece45eb04411bf448f78267e84

theorem FormalAB.V3.A10.claim_cd72a6c2 :
    type_of% @FormalAB.S160aa257.JocelynClaims.claim_cd72a6c251d46062840481043a5a8342a3ea6c334918796675f5d3745065e060 :=
  @FormalAB.S160aa257.JocelynClaims.claim_cd72a6c251d46062840481043a5a8342a3ea6c334918796675f5d3745065e060

theorem FormalAB.V3.A14.claim_3bd2c7a8 :
    type_of% @FormalAB.Sf88a75eb.JocelynClaims.claim_3bd2c7a8ad8b21e50e59f192b9262960a40a3a343511cbbc50175043f1091dea :=
  @FormalAB.Sf88a75eb.JocelynClaims.claim_3bd2c7a8ad8b21e50e59f192b9262960a40a3a343511cbbc50175043f1091dea

theorem FormalAB.V3.A14.claim_a41dd933 :
    type_of% @FormalAB.S825410c7.JocelynClaims.claim_a41dd93393d9a08f3aad11166377b156aaa1fe0de351cee181f6001f06c288b4 :=
  @FormalAB.S825410c7.JocelynClaims.claim_a41dd93393d9a08f3aad11166377b156aaa1fe0de351cee181f6001f06c288b4

theorem FormalAB.V3.A14.claim_d2b2dc1b :
    type_of% @FormalAB.S11112e11.JocelynClaims.claim_d2b2dc1bcb7fed076533b1285b9b4bb7bc334e222b2abfb65cc22473659d6587 :=
  @FormalAB.S11112e11.JocelynClaims.claim_d2b2dc1bcb7fed076533b1285b9b4bb7bc334e222b2abfb65cc22473659d6587

theorem FormalAB.V3.A15.claim_5bdb7e44 :
    type_of% @FormalAB.S9458b27c.JocelynClaims.claim_5bdb7e44508ecd490e3fe27d64b55a757b023b57dcc6fbf5bd01fad37c97eb75 :=
  @FormalAB.S9458b27c.JocelynClaims.claim_5bdb7e44508ecd490e3fe27d64b55a757b023b57dcc6fbf5bd01fad37c97eb75

theorem FormalAB.V3.A16.claim_c4c9e693 :
    type_of% @FormalAB.S48203c34.JocelynClaims.claim_c4c9e6931c637e032fa1c9e22238e389326b4d6d54570b653ebd6fd5a0bcaace :=
  @FormalAB.S48203c34.JocelynClaims.claim_c4c9e6931c637e032fa1c9e22238e389326b4d6d54570b653ebd6fd5a0bcaace

theorem FormalAB.V3.A2.claim_1230f737 :
    type_of% @FormalAB.Sab87e3d4.JocelynClaims.claim_1230f737e4649a54e9a694336c3c988db7c2a836059ef69cda8f2365d49283a6 :=
  @FormalAB.Sab87e3d4.JocelynClaims.claim_1230f737e4649a54e9a694336c3c988db7c2a836059ef69cda8f2365d49283a6

theorem FormalAB.V3.A2.claim_1d03ed08 :
    type_of% @FormalAB.Sa821b93c.JocelynClaims.claim_1d03ed089cb1d1ac3842da89e67fb142d610264b4ed34cf5399ce84e0491be5d :=
  @FormalAB.Sa821b93c.JocelynClaims.claim_1d03ed089cb1d1ac3842da89e67fb142d610264b4ed34cf5399ce84e0491be5d

theorem FormalAB.V3.A2.claim_21439041 :
    type_of% @FormalAB.S9f717b31.JocelynClaims.claim_21439041883364a940d303af8b655a0240e18e910a8e85a0434262cdbf61bff2 :=
  @FormalAB.S9f717b31.JocelynClaims.claim_21439041883364a940d303af8b655a0240e18e910a8e85a0434262cdbf61bff2

theorem FormalAB.V3.A2.claim_3ac83fa3 :
    type_of% @FormalAB.Se37df572.JocelynClaims.claim_3ac83fa3b48014ec782094529b2a46dc14d07a5e7c6ef875f150c86d020c2774 :=
  @FormalAB.Se37df572.JocelynClaims.claim_3ac83fa3b48014ec782094529b2a46dc14d07a5e7c6ef875f150c86d020c2774

theorem FormalAB.V3.A2.claim_51c0b214 :
    type_of% @FormalAB.S078e7d20.JocelynClaims.claim_51c0b2147084a3766a09c7f67cc271df449f991a6348c97c6ebaae1f259f6657 :=
  @FormalAB.S078e7d20.JocelynClaims.claim_51c0b2147084a3766a09c7f67cc271df449f991a6348c97c6ebaae1f259f6657

theorem FormalAB.V3.A2.claim_742f066e :
    type_of% @FormalAB.S3b72950f.JocelynClaims.claim_742f066ebf02c640ba81922797afbea05cf16ee5dc01c06ee0e09f7640c7f1ae :=
  @FormalAB.S3b72950f.JocelynClaims.claim_742f066ebf02c640ba81922797afbea05cf16ee5dc01c06ee0e09f7640c7f1ae

theorem FormalAB.V3.A2.claim_7c7a71be :
    type_of% @JocelynClaims_Sbe534c92.claim_7c7a71be6a5d845ed02a30e5aea8f77c7b8d6e9d1ad3b9d684cefd8036dfd7a8 :=
  @JocelynClaims_Sbe534c92.claim_7c7a71be6a5d845ed02a30e5aea8f77c7b8d6e9d1ad3b9d684cefd8036dfd7a8

theorem FormalAB.V3.A2.claim_9a871236 :
    type_of% @FormalAB.S4f28eb05.JocelynClaims.claim_9a8712369fb366b34975f200080267e50d5a4a7c9edcaf7502318f27864add4e :=
  @FormalAB.S4f28eb05.JocelynClaims.claim_9a8712369fb366b34975f200080267e50d5a4a7c9edcaf7502318f27864add4e

theorem FormalAB.V3.A2.claim_da2a60c4 :
    type_of% @JocelynClaims_Se3ca258b.claim_da2a60c4963f695b0510075903b0b34c350e30c0b78ae6384fbf7d0694730258 :=
  @JocelynClaims_Se3ca258b.claim_da2a60c4963f695b0510075903b0b34c350e30c0b78ae6384fbf7d0694730258

theorem FormalAB.V3.A3.claim_0ac5d0a6 :
    type_of% @FormalAB.Sb5ac3c34.JocelynClaims.claim_0ac5d0a636703f91f4ce1b7a0d0739f3e93bd31fff4b51b4a6f90c29d2abd606 :=
  @FormalAB.Sb5ac3c34.JocelynClaims.claim_0ac5d0a636703f91f4ce1b7a0d0739f3e93bd31fff4b51b4a6f90c29d2abd606

theorem FormalAB.V3.A3.claim_0b93a534 :
    type_of% @FormalAB.Sac09a8d3.JocelynClaims.claim_0b93a5343455892d7c3029c8193da28f2424ae4f6b07508fe200da1990505e11 :=
  @FormalAB.Sac09a8d3.JocelynClaims.claim_0b93a5343455892d7c3029c8193da28f2424ae4f6b07508fe200da1990505e11

theorem FormalAB.V3.A3.claim_0d45803d :
    type_of% @FormalAB.S11c3682d.JocelynClaims.claim_0d45803d5269a373b541031abad5447b3fd9b9ae32301db05b623b6a17133b0e :=
  @FormalAB.S11c3682d.JocelynClaims.claim_0d45803d5269a373b541031abad5447b3fd9b9ae32301db05b623b6a17133b0e

theorem FormalAB.V3.A3.claim_0fec6153 :
    type_of% @FormalAB.Sdaed3871.JocelynClaims.claim_0fec61537605e13397e716d2a2765ec66c2e13a9a7e70cbd00da70117765e6bc :=
  @FormalAB.Sdaed3871.JocelynClaims.claim_0fec61537605e13397e716d2a2765ec66c2e13a9a7e70cbd00da70117765e6bc

theorem FormalAB.V3.A3.claim_1338b05d :
    type_of% @FormalAB.S4090edd7.JocelynClaims.claim_1338b05d7aa2389cd84f49897a9473f0096b7968f61a6d13c657c4896d12a503 :=
  @FormalAB.S4090edd7.JocelynClaims.claim_1338b05d7aa2389cd84f49897a9473f0096b7968f61a6d13c657c4896d12a503

theorem FormalAB.V3.A3.claim_175ec88b :
    type_of% @FormalAB.Scc53d7e3.JocelynClaims.claim_175ec88bb39f47588134facd86717dc6cccc0f5f8b27cb344e1be2b4a0033d5f :=
  @FormalAB.Scc53d7e3.JocelynClaims.claim_175ec88bb39f47588134facd86717dc6cccc0f5f8b27cb344e1be2b4a0033d5f

theorem FormalAB.V3.A3.claim_1b77702a :
    type_of% @FormalAB.S4926c1f4.JocelynClaims.claim_1b77702a6c569ddc2f902728e440960405397a6d975bf8544d0a60768dedc0a7 :=
  @FormalAB.S4926c1f4.JocelynClaims.claim_1b77702a6c569ddc2f902728e440960405397a6d975bf8544d0a60768dedc0a7

theorem FormalAB.V3.A3.claim_2158e4ad :
    type_of% @FormalAB.S109f3370.JocelynClaims.claim_2158e4ad4d39f85f105dc6716964ba74253a502c238e48e654101c966ef8ccfa :=
  @FormalAB.S109f3370.JocelynClaims.claim_2158e4ad4d39f85f105dc6716964ba74253a502c238e48e654101c966ef8ccfa

theorem FormalAB.V3.A3.claim_2da1a444 :
    type_of% @FormalAB.S2350ff1c.JocelynClaims.claim_2da1a4442f18626153467667aa7c1d9578f0d93ad599594d646ad0b783dc58fa :=
  @FormalAB.S2350ff1c.JocelynClaims.claim_2da1a4442f18626153467667aa7c1d9578f0d93ad599594d646ad0b783dc58fa

theorem FormalAB.V3.A3.claim_373b1bb6 :
    type_of% @FormalAB.Sd1b1f61f.JocelynClaims.claim_373b1bb6384808aa7b4f7cbf6eec00cb107372b69fae61a32f6b6f3004f96f78 :=
  @FormalAB.Sd1b1f61f.JocelynClaims.claim_373b1bb6384808aa7b4f7cbf6eec00cb107372b69fae61a32f6b6f3004f96f78

theorem FormalAB.V3.A3.claim_3933e025 :
    type_of% @FormalAB.S69647171.JocelynClaims.claim_3933e02500c496c34ddc43ea34742c3635fe5e6a85e59b6ba30d9dd04bda8000 :=
  @FormalAB.S69647171.JocelynClaims.claim_3933e02500c496c34ddc43ea34742c3635fe5e6a85e59b6ba30d9dd04bda8000

theorem FormalAB.V3.A3.claim_484dfd1f :
    type_of% @FormalAB.Sbcd28934.JocelynClaims.claim_484dfd1f58a15caccaaaa0bf5cc5160a0127e432fd42be7ffec8fe1bd3d66d08 :=
  @FormalAB.Sbcd28934.JocelynClaims.claim_484dfd1f58a15caccaaaa0bf5cc5160a0127e432fd42be7ffec8fe1bd3d66d08

theorem FormalAB.V3.A3.claim_5116a9f7 :
    type_of% @FormalAB.S1bd2d745.JocelynClaims.claim_5116a9f79d2da2bf6321ca2ae10f925d8b9676b4d6a4f32c6b308a84d70b3e0c :=
  @FormalAB.S1bd2d745.JocelynClaims.claim_5116a9f79d2da2bf6321ca2ae10f925d8b9676b4d6a4f32c6b308a84d70b3e0c

theorem FormalAB.V3.A3.claim_5d53fdc9 :
    type_of% @FormalAB.S6e12aa43.JocelynClaims.claim_5d53fdc96b534fef09898d9f8dceca14a87a60c50dcb87c63675921c3c1e50d0 :=
  @FormalAB.S6e12aa43.JocelynClaims.claim_5d53fdc96b534fef09898d9f8dceca14a87a60c50dcb87c63675921c3c1e50d0

theorem FormalAB.V3.A3.claim_70b2552e :
    type_of% @FormalAB.S96394400.JocelynClaims.claim_70b2552e0f57232a0031656a3df0e3857d8e732f50cb0228a418af0101c04e33 :=
  @FormalAB.S96394400.JocelynClaims.claim_70b2552e0f57232a0031656a3df0e3857d8e732f50cb0228a418af0101c04e33

theorem FormalAB.V3.A3.claim_712c43b6 :
    type_of% @FormalAB.S0430ca7c.JocelynClaims.claim_712c43b6e8b6f45b875ef48d2866228ec38f240debb306618fa18462aaa62c6c :=
  @FormalAB.S0430ca7c.JocelynClaims.claim_712c43b6e8b6f45b875ef48d2866228ec38f240debb306618fa18462aaa62c6c

theorem FormalAB.V3.A3.claim_72e21470 :
    type_of% @FormalAB.S208b505c.JocelynClaims.claim_72e2147069463c37527f8647f2fc1affdab5588f9ccfd88eb557cfcd45056f56 :=
  @FormalAB.S208b505c.JocelynClaims.claim_72e2147069463c37527f8647f2fc1affdab5588f9ccfd88eb557cfcd45056f56

theorem FormalAB.V3.A3.claim_77234083 :
    type_of% @FormalAB.S3a9f242c.JocelynClaims.claim_77234083b98cf2fa98db2bbaebb26e94191c114af6823acd7c65cf94145dd336 :=
  @FormalAB.S3a9f242c.JocelynClaims.claim_77234083b98cf2fa98db2bbaebb26e94191c114af6823acd7c65cf94145dd336

theorem FormalAB.V3.A3.claim_84ae2eb5 :
    type_of% @FormalAB.S7d3914ac.JocelynClaims.claim_84ae2eb54a1990451db292dbe4e667b093a1ae115d5814ef4364ef56097697bd :=
  @FormalAB.S7d3914ac.JocelynClaims.claim_84ae2eb54a1990451db292dbe4e667b093a1ae115d5814ef4364ef56097697bd

theorem FormalAB.V3.A3.claim_92f307c8 :
    type_of% @FormalAB.S4be11d8f.JocelynClaims.claim_92f307c85224b8df14698813eed7b6d58d5c48bbfd0f140f4f4fdc3f69f5b793 :=
  @FormalAB.S4be11d8f.JocelynClaims.claim_92f307c85224b8df14698813eed7b6d58d5c48bbfd0f140f4f4fdc3f69f5b793

theorem FormalAB.V3.A3.claim_984021bc :
    type_of% @FormalAB.S8f583f42.JocelynClaims.claim_984021bcd793eb74c1565b3cc870c241be60f4a90a29b9fc14bc13ecc0b94183 :=
  @FormalAB.S8f583f42.JocelynClaims.claim_984021bcd793eb74c1565b3cc870c241be60f4a90a29b9fc14bc13ecc0b94183

theorem FormalAB.V3.A3.claim_98caf96f :
    type_of% @FormalAB.Sfeca7c5b.JocelynClaims.claim_98caf96f472d39474a06c34c310fc397f7d812f5d8d5f9bc531bceee8c63e385 :=
  @FormalAB.Sfeca7c5b.JocelynClaims.claim_98caf96f472d39474a06c34c310fc397f7d812f5d8d5f9bc531bceee8c63e385

theorem FormalAB.V3.A3.claim_a784ea0d :
    type_of% @FormalAB.S7c60f425.JocelynClaims.claim_a784ea0d4882079f077167e52b8b095db4d6b6a3bb097a313cf37b8ae344b161 :=
  @FormalAB.S7c60f425.JocelynClaims.claim_a784ea0d4882079f077167e52b8b095db4d6b6a3bb097a313cf37b8ae344b161

theorem FormalAB.V3.A3.claim_b772e333 :
    type_of% @FormalAB.S9589feb3.JocelynClaims.claim_b772e333ec3453d3efe015aac3721fd5d153237d05f5a62cd04f2cf50b56e95d :=
  @FormalAB.S9589feb3.JocelynClaims.claim_b772e333ec3453d3efe015aac3721fd5d153237d05f5a62cd04f2cf50b56e95d

theorem FormalAB.V3.A3.claim_c03aedc6 :
    type_of% @FormalAB.S376bcb36.JocelynClaims.claim_c03aedc6541755be830df7c7e828a7025b119d896416be0354baa4bcb894ef9d :=
  @FormalAB.S376bcb36.JocelynClaims.claim_c03aedc6541755be830df7c7e828a7025b119d896416be0354baa4bcb894ef9d

theorem FormalAB.V3.A3.claim_d59439ab :
    type_of% @FormalAB.S17759d9f.JocelynClaims.claim_d59439ab84a1b0bfc24753d6302a9e46d8e7ac23d153c442b375879e37f6fa4d :=
  @FormalAB.S17759d9f.JocelynClaims.claim_d59439ab84a1b0bfc24753d6302a9e46d8e7ac23d153c442b375879e37f6fa4d

theorem FormalAB.V3.A3.claim_da77e57e :
    type_of% @FormalAB.Saedfe0d7.JocelynClaims.claim_da77e57e1c1d93403eb86effcaf10dfaa6c6f911e24571deee05676c2cdbce17 :=
  @FormalAB.Saedfe0d7.JocelynClaims.claim_da77e57e1c1d93403eb86effcaf10dfaa6c6f911e24571deee05676c2cdbce17

theorem FormalAB.V3.A3.claim_ea314455 :
    type_of% @FormalAB.Sc8731f9d.JocelynClaims.claim_ea314455809978934d8a98061e79710124c8b05a7df40f29f7178fbfe799111a :=
  @FormalAB.Sc8731f9d.JocelynClaims.claim_ea314455809978934d8a98061e79710124c8b05a7df40f29f7178fbfe799111a

theorem FormalAB.V3.A3.claim_fd0ef918 :
    type_of% @FormalAB.S4a0fdf45.JocelynClaims.claim_fd0ef918c85ea875105264b8e0ca5ddc9bc77b3a051415001a363ffccaad28da :=
  @FormalAB.S4a0fdf45.JocelynClaims.claim_fd0ef918c85ea875105264b8e0ca5ddc9bc77b3a051415001a363ffccaad28da

theorem FormalAB.V3.A4.claim_08116d8a :
    type_of% @FormalAB.S59b58d62.JocelynClaims.claim_08116d8ac79e177090122a17c61671570e902e0cbf31fb150172b1c1c0fea2ec :=
  @FormalAB.S59b58d62.JocelynClaims.claim_08116d8ac79e177090122a17c61671570e902e0cbf31fb150172b1c1c0fea2ec

theorem FormalAB.V3.A4.claim_395c7f40 :
    type_of% @FormalAB.S4655eae1.JocelynClaims.claim_395c7f40cd8bd755bff1cf0dc26b4512f1b228e8459757dc3d248c7496e974a0 :=
  @FormalAB.S4655eae1.JocelynClaims.claim_395c7f40cd8bd755bff1cf0dc26b4512f1b228e8459757dc3d248c7496e974a0

theorem FormalAB.V3.A4.claim_633b6513 :
    type_of% @FormalAB.Sd55d8b9f.JocelynClaims.claim_633b65137dceceb2039f41d452412c7205c0a67249c4b8f6793aeb745b4e0550 :=
  @FormalAB.Sd55d8b9f.JocelynClaims.claim_633b65137dceceb2039f41d452412c7205c0a67249c4b8f6793aeb745b4e0550

theorem FormalAB.V3.A5.claim_0357db81 :
    type_of% @FormalAB.Sec169b78.JocelynClaims.claim_0357db812536f4b6cb95b812ac7fe480c3f6951543bd0d23ce7fef93a4c0b67e :=
  @FormalAB.Sec169b78.JocelynClaims.claim_0357db812536f4b6cb95b812ac7fe480c3f6951543bd0d23ce7fef93a4c0b67e

theorem FormalAB.V3.A5.claim_072c3a6e :
    type_of% @FormalAB.S9ad0e971.JocelynClaims.claim_072c3a6e176b78db60bf95e8903e8cfa8eacb7f3a1e5fb7013de3d8dc1ff1087 :=
  @FormalAB.S9ad0e971.JocelynClaims.claim_072c3a6e176b78db60bf95e8903e8cfa8eacb7f3a1e5fb7013de3d8dc1ff1087

theorem FormalAB.V3.A5.claim_0c2dc82a :
    type_of% @FormalAB.S93135965.JocelynClaims.claim_0c2dc82a21e24342e1a76dd17dd8d1d102641755f12b4b2aa7895bbdc7ec2b1a :=
  @FormalAB.S93135965.JocelynClaims.claim_0c2dc82a21e24342e1a76dd17dd8d1d102641755f12b4b2aa7895bbdc7ec2b1a

theorem FormalAB.V3.A5.claim_0e0d90b2 :
    type_of% @FormalAB.Sb751f117.JocelynClaims.claim_0e0d90b2880ea02d44c5114db421fe5f89b5e06d231ac9de0696576f68d66e70 :=
  @FormalAB.Sb751f117.JocelynClaims.claim_0e0d90b2880ea02d44c5114db421fe5f89b5e06d231ac9de0696576f68d66e70

theorem FormalAB.V3.A5.claim_0e87df01 :
    type_of% @FormalAB.Sc577efcd.JocelynClaims.claim_0e87df013ff6ff87c8e1417f336c3d7af8b88e3c61ced563738f8f3a7529574a :=
  @FormalAB.Sc577efcd.JocelynClaims.claim_0e87df013ff6ff87c8e1417f336c3d7af8b88e3c61ced563738f8f3a7529574a

theorem FormalAB.V3.A5.claim_14815d4d :
    type_of% @FormalAB.S25f5c02a.JocelynClaims.claim_14815d4dd0678e1313331e16716225b64fac0c3a8277eb5dc212df6b7eb966f6 :=
  @FormalAB.S25f5c02a.JocelynClaims.claim_14815d4dd0678e1313331e16716225b64fac0c3a8277eb5dc212df6b7eb966f6

theorem FormalAB.V3.A5.claim_19a4c2ff :
    type_of% @FormalAB.Sb868eaea.JocelynClaims.claim_19a4c2ffed9b340e17395110c7b1dcba479532e67683e9afaa4faacca8fa8fe3 :=
  @FormalAB.Sb868eaea.JocelynClaims.claim_19a4c2ffed9b340e17395110c7b1dcba479532e67683e9afaa4faacca8fa8fe3

theorem FormalAB.V3.A5.claim_1f317d8a :
    type_of% @FormalAB.Sa48e2d62.JocelynClaims.claim_1f317d8a0ffba478c1a12b9c2eafe76b2342b63f773dd5317c6286b87b302a5e :=
  @FormalAB.Sa48e2d62.JocelynClaims.claim_1f317d8a0ffba478c1a12b9c2eafe76b2342b63f773dd5317c6286b87b302a5e

theorem FormalAB.V3.A5.claim_23901e5a :
    type_of% @FormalAB.S03b2acad.JocelynClaims.claim_23901e5a643bd6f3764df51b1a387d0e23f431c522eaa8213ba45390c29b2129 :=
  @FormalAB.S03b2acad.JocelynClaims.claim_23901e5a643bd6f3764df51b1a387d0e23f431c522eaa8213ba45390c29b2129

theorem FormalAB.V3.A5.claim_2678fcf1 :
    type_of% @FormalAB.Sbefdd95b.JocelynClaims.claim_2678fcf1fbb37777e4e056cb95382a9f88451aa0d7426c86591354bb469cdd7d :=
  @FormalAB.Sbefdd95b.JocelynClaims.claim_2678fcf1fbb37777e4e056cb95382a9f88451aa0d7426c86591354bb469cdd7d

theorem FormalAB.V3.A5.claim_287eb866 :
    type_of% @FormalAB.S1e7cf533.JocelynClaims.claim_287eb866adc2d67945fea88c239b3b43dea6d99da93af88ab6c0e2de88caf71a :=
  @FormalAB.S1e7cf533.JocelynClaims.claim_287eb866adc2d67945fea88c239b3b43dea6d99da93af88ab6c0e2de88caf71a

theorem FormalAB.V3.A5.claim_2b8ac916 :
    type_of% @FormalAB.S84900580.JocelynClaims.claim_2b8ac91602fe64e089091d8d20e132480a4cb95949fea0e4eac983fc322adece :=
  @FormalAB.S84900580.JocelynClaims.claim_2b8ac91602fe64e089091d8d20e132480a4cb95949fea0e4eac983fc322adece

theorem FormalAB.V3.A5.claim_2cd2ef85 :
    type_of% @FormalAB.S877de5f3.JocelynClaims.claim_2cd2ef851fa1f1c81ce0d9da2ac06c2f3b280681bf237c1ee9ef030425ddf711 :=
  @FormalAB.S877de5f3.JocelynClaims.claim_2cd2ef851fa1f1c81ce0d9da2ac06c2f3b280681bf237c1ee9ef030425ddf711

theorem FormalAB.V3.A5.claim_2d43455f :
    type_of% @FormalAB.S40fa8f3f.JocelynClaims.claim_2d43455f516ebd78faf8e58524e1956b587acc87ecd2f9b64ce63a81e5234896 :=
  @FormalAB.S40fa8f3f.JocelynClaims.claim_2d43455f516ebd78faf8e58524e1956b587acc87ecd2f9b64ce63a81e5234896

theorem FormalAB.V3.A5.claim_38b3ece0 :
    type_of% @FormalAB.Sa57df17a.JocelynClaims.claim_38b3ece0876ba8e7eb5509d6e33bcf9b65b705370f7fb7d9f7ada061cce3632a :=
  @FormalAB.Sa57df17a.JocelynClaims.claim_38b3ece0876ba8e7eb5509d6e33bcf9b65b705370f7fb7d9f7ada061cce3632a

theorem FormalAB.V3.A5.claim_3e75905b :
    type_of% @FormalAB.Sa3e85b88.JocelynClaims.claim_3e75905b2d0f06455e160821601d7b7ded491039a7f5b69aba31febcf9b0c31f :=
  @FormalAB.Sa3e85b88.JocelynClaims.claim_3e75905b2d0f06455e160821601d7b7ded491039a7f5b69aba31febcf9b0c31f

theorem FormalAB.V3.A5.claim_4a7d238a :
    type_of% @FormalAB.S9511d4c3.JocelynClaims.claim_4a7d238a4cffdd20a158e2752d96d1d9b50c291946b63cc33f54d148543b5ba7 :=
  @FormalAB.S9511d4c3.JocelynClaims.claim_4a7d238a4cffdd20a158e2752d96d1d9b50c291946b63cc33f54d148543b5ba7

theorem FormalAB.V3.A5.claim_53f3d9f5 :
    type_of% @FormalAB.S93d0e676.JocelynClaims.claim_53f3d9f5455cb696b516eb76799e3ae2b586d026e3af7a5e06cbff26e8b1545a :=
  @FormalAB.S93d0e676.JocelynClaims.claim_53f3d9f5455cb696b516eb76799e3ae2b586d026e3af7a5e06cbff26e8b1545a

theorem FormalAB.V3.A5.claim_5e2cfce1 :
    type_of% @FormalAB.S50193082.JocelynClaims.claim_5e2cfce14f69ab1167285bdf0a8de30de2eb248ddaeea887f37cd9ab1741ba52 :=
  @FormalAB.S50193082.JocelynClaims.claim_5e2cfce14f69ab1167285bdf0a8de30de2eb248ddaeea887f37cd9ab1741ba52

theorem FormalAB.V3.A5.claim_5e5f95b6 :
    type_of% @FormalAB.S6aa76dac.JocelynClaims.claim_5e5f95b63cee1d95abb2f527622e1aca769928e97fb6581115c612fe53cb5477 :=
  @FormalAB.S6aa76dac.JocelynClaims.claim_5e5f95b63cee1d95abb2f527622e1aca769928e97fb6581115c612fe53cb5477

theorem FormalAB.V3.A5.claim_61abb56d :
    type_of% @FormalAB.Sb23c796c.JocelynClaims.claim_61abb56d777f10b8c4c7fb56cb439980c51b50b31e1f22ff1783b1eadefdfeda :=
  @FormalAB.Sb23c796c.JocelynClaims.claim_61abb56d777f10b8c4c7fb56cb439980c51b50b31e1f22ff1783b1eadefdfeda

theorem FormalAB.V3.A5.claim_6810bebe :
    type_of% @FormalAB.Se059a44d.JocelynClaims.claim_6810bebe9f46765c742849f788f15b91cd6290a518eefedd90044a19dfdd4207 :=
  @FormalAB.Se059a44d.JocelynClaims.claim_6810bebe9f46765c742849f788f15b91cd6290a518eefedd90044a19dfdd4207

theorem FormalAB.V3.A5.claim_6e81562a :
    type_of% @FormalAB.S75c3b853.JocelynClaims.claim_6e81562a9f7d5990a9cc1764fca06b4768537a722660e4413df9e5061e1e94ab :=
  @FormalAB.S75c3b853.JocelynClaims.claim_6e81562a9f7d5990a9cc1764fca06b4768537a722660e4413df9e5061e1e94ab

theorem FormalAB.V3.A5.claim_7b9ec90d :
    type_of% @FormalAB.Sc7482db2.JocelynClaims.claim_7b9ec90da7f52c469929ec338d6f7e28ea07d631f744cb275458672918f7aee7 :=
  @FormalAB.Sc7482db2.JocelynClaims.claim_7b9ec90da7f52c469929ec338d6f7e28ea07d631f744cb275458672918f7aee7

theorem FormalAB.V3.A5.claim_865afc15 :
    type_of% @FormalAB.Sb4a69aed.JocelynClaims.claim_865afc155d79460ad2c12968c3a161c0b4b5cbe21101703a05307c82603bc9ce :=
  @FormalAB.Sb4a69aed.JocelynClaims.claim_865afc155d79460ad2c12968c3a161c0b4b5cbe21101703a05307c82603bc9ce

theorem FormalAB.V3.A5.claim_a56f2f4f :
    type_of% @FormalAB.Se7122579.JocelynClaims.claim_a56f2f4f893ffc515106991e7dc7f0dd181afccf691aab84e39ac52bf1f32353 :=
  @FormalAB.Se7122579.JocelynClaims.claim_a56f2f4f893ffc515106991e7dc7f0dd181afccf691aab84e39ac52bf1f32353

theorem FormalAB.V3.A5.claim_ab923dcf :
    type_of% @FormalAB.S54b4417b.JocelynClaims.claim_ab923dcf84e9dc87fc5a903dad25d08370ead3efaa3aa1e11af645e658b00e7d :=
  @FormalAB.S54b4417b.JocelynClaims.claim_ab923dcf84e9dc87fc5a903dad25d08370ead3efaa3aa1e11af645e658b00e7d

theorem FormalAB.V3.A5.claim_ad943653 :
    type_of% @FormalAB.S48c923c1.JocelynClaims.claim_ad943653babc9fc0202de5d0410b9c73f58141ac05bd56b58862b151978e8619 :=
  @FormalAB.S48c923c1.JocelynClaims.claim_ad943653babc9fc0202de5d0410b9c73f58141ac05bd56b58862b151978e8619

theorem FormalAB.V3.A5.claim_b122a395 :
    type_of% @FormalAB.S6cc5a3e3.JocelynClaims.claim_b122a3959fbb1c60f1f340ba5583deb7f53f3ad1a8d15de66377002ac64a25ba :=
  @FormalAB.S6cc5a3e3.JocelynClaims.claim_b122a3959fbb1c60f1f340ba5583deb7f53f3ad1a8d15de66377002ac64a25ba

theorem FormalAB.V3.A5.claim_b20fb00c :
    type_of% @FormalAB.Sd00ed590.JocelynClaims.claim_b20fb00c289b46c6cb005003d0e0086120eafd6e44eca3aad0e9eee1f8d7564f :=
  @FormalAB.Sd00ed590.JocelynClaims.claim_b20fb00c289b46c6cb005003d0e0086120eafd6e44eca3aad0e9eee1f8d7564f

theorem FormalAB.V3.A5.claim_b5c8fea4 :
    type_of% @FormalAB.Sa461fe12.JocelynClaims.claim_b5c8fea4b0e65ed2f7f25afc46786de245702559815af4387922150b1ac219bf :=
  @FormalAB.Sa461fe12.JocelynClaims.claim_b5c8fea4b0e65ed2f7f25afc46786de245702559815af4387922150b1ac219bf

theorem FormalAB.V3.A5.claim_b688d346 :
    type_of% @FormalAB.S9652ac8c.JocelynClaims.claim_b688d3468795996705e36a83d4c909f15e20f0b7c34b9fd3e12d5eed828c6122 :=
  @FormalAB.S9652ac8c.JocelynClaims.claim_b688d3468795996705e36a83d4c909f15e20f0b7c34b9fd3e12d5eed828c6122

theorem FormalAB.V3.A5.claim_ceaa0968 :
    type_of% @FormalAB.S25167265.JocelynClaims.claim_ceaa0968be5cd77bdecfc100f0fb0d157990b41c00713d53f42891a3f5db48d8 :=
  @FormalAB.S25167265.JocelynClaims.claim_ceaa0968be5cd77bdecfc100f0fb0d157990b41c00713d53f42891a3f5db48d8

theorem FormalAB.V3.A5.claim_d0c95779 :
    type_of% @FormalAB.S1b64778e.JocelynClaims.claim_d0c95779bd7ac30aaa90878cabdc0635d301505dd3f7d8349cc158cbab5d752a :=
  @FormalAB.S1b64778e.JocelynClaims.claim_d0c95779bd7ac30aaa90878cabdc0635d301505dd3f7d8349cc158cbab5d752a

theorem FormalAB.V3.A5.claim_e20043e8 :
    type_of% @FormalAB.S2b84589f.JocelynClaims.claim_e20043e877cc7f6fa915f18cc7590809a6d647a0fe0e66aac9caa124288a4f2a :=
  @FormalAB.S2b84589f.JocelynClaims.claim_e20043e877cc7f6fa915f18cc7590809a6d647a0fe0e66aac9caa124288a4f2a

theorem FormalAB.V3.A5.claim_e604428f :
    type_of% @FormalAB.Sa00cb9c7.JocelynClaims.claim_e604428fdf2bb81ef95ff520d63a55660ad9e32794f342878313cd49da8b389e :=
  @FormalAB.Sa00cb9c7.JocelynClaims.claim_e604428fdf2bb81ef95ff520d63a55660ad9e32794f342878313cd49da8b389e

theorem FormalAB.V3.A5.claim_e8bb8e0b :
    type_of% @FormalAB.S72392b81.JocelynClaims.claim_e8bb8e0b462198fe17c1922e04cabbde342a7da1d841c3a8181ba20a4d166b41 :=
  @FormalAB.S72392b81.JocelynClaims.claim_e8bb8e0b462198fe17c1922e04cabbde342a7da1d841c3a8181ba20a4d166b41

theorem FormalAB.V3.A5.claim_f1bb8d60 :
    type_of% @FormalAB.S124d1a75.JocelynClaims.claim_f1bb8d6058da833b00db6625a2e5500f38cdecb7388366ed378cde5c35977324 :=
  @FormalAB.S124d1a75.JocelynClaims.claim_f1bb8d6058da833b00db6625a2e5500f38cdecb7388366ed378cde5c35977324

theorem FormalAB.V3.A5.claim_f3b6022b :
    type_of% @FormalAB.S4e61b76c.JocelynClaims.claim_f3b6022b8bde1b85dbbaf7368871beacef81e07a3289a93a0c72e9454b23d749 :=
  @FormalAB.S4e61b76c.JocelynClaims.claim_f3b6022b8bde1b85dbbaf7368871beacef81e07a3289a93a0c72e9454b23d749

theorem FormalAB.V3.A5.claim_f89c0899 :
    type_of% @FormalAB.Sa9c18fe1.JocelynClaims.claim_f89c08996a8df6ac6a9e24fefe718036c2f7e375653856d50904d52bd19c93cc :=
  @FormalAB.Sa9c18fe1.JocelynClaims.claim_f89c08996a8df6ac6a9e24fefe718036c2f7e375653856d50904d52bd19c93cc

theorem FormalAB.V3.A5.claim_f9442b33 :
    type_of% @FormalAB.Sf885170c.JocelynClaims.claim_f9442b33ae2c6962df23f17267f2ed3f6c8af39504cfef536ba7635c8ed30223 :=
  @FormalAB.Sf885170c.JocelynClaims.claim_f9442b33ae2c6962df23f17267f2ed3f6c8af39504cfef536ba7635c8ed30223

theorem FormalAB.V3.A5.claim_fcd80658 :
    type_of% @FormalAB.S5a5b0bd5.JocelynClaims.claim_fcd806582eb6476367651c9b465c2bcc8589ade4ab91ca64831d3136f30966d6 :=
  @FormalAB.S5a5b0bd5.JocelynClaims.claim_fcd806582eb6476367651c9b465c2bcc8589ade4ab91ca64831d3136f30966d6

theorem FormalAB.V3.A9.claim_6b6169cb :
    type_of% @FormalAB.S65df95e8.JocelynClaims.claim_6b6169cbc7077fa9ae6ddb0aab9241d3c391a13017f48af78af3193ce28570c1 :=
  @FormalAB.S65df95e8.JocelynClaims.claim_6b6169cbc7077fa9ae6ddb0aab9241d3c391a13017f48af78af3193ce28570c1

theorem FormalAB.V3.B2.claim_27791283 :
    type_of% @FormalAB.S77dab681.JocelynClaims.claim_277912837327a9fee084263006401f8719d6e10b8d522fdf1c2de2cb564c4fcf :=
  @FormalAB.S77dab681.JocelynClaims.claim_277912837327a9fee084263006401f8719d6e10b8d522fdf1c2de2cb564c4fcf

theorem FormalAB.V3.B2.claim_2e3e6a01 :
    type_of% @FormalAB.S7f3fefed.JocelynClaims.claim_2e3e6a01470a0c1eed635f800b7ea3ceb23a4a50b6b278bf22f92052dfbc1f4e :=
  @FormalAB.S7f3fefed.JocelynClaims.claim_2e3e6a01470a0c1eed635f800b7ea3ceb23a4a50b6b278bf22f92052dfbc1f4e

theorem FormalAB.V3.B2.claim_8af16931 :
    type_of% @FormalAB.S7510344d.JocelynClaims.claim_8af1693149890427ed34b7d46d7c217114f651510d33e75fac7c4e4b7d3b4e71 :=
  @FormalAB.S7510344d.JocelynClaims.claim_8af1693149890427ed34b7d46d7c217114f651510d33e75fac7c4e4b7d3b4e71

theorem FormalAB.V3.B2.claim_aad375aa :
    type_of% @FormalAB.S9ac83253.JocelynClaims.claim_aad375aa01792b4254d3383bf7ff0a0b6f971e010ad081405d35710d165ab5ec :=
  @FormalAB.S9ac83253.JocelynClaims.claim_aad375aa01792b4254d3383bf7ff0a0b6f971e010ad081405d35710d165ab5ec

theorem FormalAB.V3.B2.claim_cd250df0 :
    type_of% @FormalAB.S31134e0c.JocelynClaims.claim_cd250df096a304f9b4098d31e4436451bd3fc36dd6db3f48de406fc8306912eb :=
  @FormalAB.S31134e0c.JocelynClaims.claim_cd250df096a304f9b4098d31e4436451bd3fc36dd6db3f48de406fc8306912eb

theorem FormalAB.V3.B2.claim_cef5977e :
    type_of% @FormalAB.S62e9dae0.JocelynClaims.claim_cef5977ef8abbec41632b622de4699c51b5cf678b181338339f3dedab773884f :=
  @FormalAB.S62e9dae0.JocelynClaims.claim_cef5977ef8abbec41632b622de4699c51b5cf678b181338339f3dedab773884f

theorem FormalAB.V3.B2.claim_fafe8b94 :
    type_of% @FormalAB.Sbeb334b1.JocelynClaims.claim_fafe8b94778a29c9a0298e44df80fe62948d7b7bde03c8020d961429afe11d8d :=
  @FormalAB.Sbeb334b1.JocelynClaims.claim_fafe8b94778a29c9a0298e44df80fe62948d7b7bde03c8020d961429afe11d8d

theorem FormalAB.V3.LP2.claim_1e64f434 :
    type_of% @FormalAB.S30f04f02.JocelynClaims.claim_1e64f434b0c9b60b9caa72899c6b68d15353e598ddc901840822c79a4efb405e :=
  @FormalAB.S30f04f02.JocelynClaims.claim_1e64f434b0c9b60b9caa72899c6b68d15353e598ddc901840822c79a4efb405e

theorem FormalAB.V3.LP2.claim_4c7df99c :
    type_of% @FormalAB.S1a1f3383.JocelynClaims.claim_4c7df99c3484e2f6d5afa731852b94f60f5fe51670ee2bdeb218c1ae4f6c2126 :=
  @FormalAB.S1a1f3383.JocelynClaims.claim_4c7df99c3484e2f6d5afa731852b94f60f5fe51670ee2bdeb218c1ae4f6c2126

theorem FormalAB.V3.Support.claim_1de98d72 :
    type_of% @FormalAB.Sd48e6c9f.JocelynClaims.claim_1de98d725356b9aaddaad6d799064b07a13a30a1f8720f8c63131e60053ab58b :=
  @FormalAB.Sd48e6c9f.JocelynClaims.claim_1de98d725356b9aaddaad6d799064b07a13a30a1f8720f8c63131e60053ab58b

theorem FormalAB.V3.Support.claim_5a6f6abe :
    type_of% @FormalAB.Sd96a648f.JocelynClaims.claim_5a6f6abe22d40980c33d15fbbf47eb56126444df3a0c72abae6f64be3986b2ac :=
  @FormalAB.Sd96a648f.JocelynClaims.claim_5a6f6abe22d40980c33d15fbbf47eb56126444df3a0c72abae6f64be3986b2ac

theorem FormalAB.V3.Support.claim_889ff89c :
    type_of% @FormalAB.S296108af.JocelynClaims.claim_889ff89cc018f356491a8b61f74a7453a9098b478b79b1571747ce8849dd849d :=
  @FormalAB.S296108af.JocelynClaims.claim_889ff89cc018f356491a8b61f74a7453a9098b478b79b1571747ce8849dd849d

theorem FormalAB.V3.Support.claim_a324027a :
    type_of% @FormalAB.Sca0547c8.JocelynClaims.claim_a324027a49750a101d9e689f59feea4b9cd16a567993923e609d632ba8f0a752 :=
  @FormalAB.Sca0547c8.JocelynClaims.claim_a324027a49750a101d9e689f59feea4b9cd16a567993923e609d632ba8f0a752
