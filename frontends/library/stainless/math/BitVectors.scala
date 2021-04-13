/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package math

import stainless.annotation._
import scala.collection.immutable.BitSet
import scala.language.implicitConversions

// TODO: write the Scala implementation

@library
@ignore
object BitVectors {

  sealed abstract class BVKind

  object i1 extends BVKind
  object i2 extends BVKind
  object i3 extends BVKind
  object i4 extends BVKind
  object i5 extends BVKind
  object i6 extends BVKind
  object i7 extends BVKind
  object i8 extends BVKind
  object i9 extends BVKind
  object i10 extends BVKind
  object i11 extends BVKind
  object i12 extends BVKind
  object i13 extends BVKind
  object i14 extends BVKind
  object i15 extends BVKind
  object i16 extends BVKind
  object i17 extends BVKind
  object i18 extends BVKind
  object i19 extends BVKind
  object i20 extends BVKind
  object i21 extends BVKind
  object i22 extends BVKind
  object i23 extends BVKind
  object i24 extends BVKind
  object i25 extends BVKind
  object i26 extends BVKind
  object i27 extends BVKind
  object i28 extends BVKind
  object i29 extends BVKind
  object i30 extends BVKind
  object i31 extends BVKind
  object i32 extends BVKind
  object i33 extends BVKind
  object i34 extends BVKind
  object i35 extends BVKind
  object i36 extends BVKind
  object i37 extends BVKind
  object i38 extends BVKind
  object i39 extends BVKind
  object i40 extends BVKind
  object i41 extends BVKind
  object i42 extends BVKind
  object i43 extends BVKind
  object i44 extends BVKind
  object i45 extends BVKind
  object i46 extends BVKind
  object i47 extends BVKind
  object i48 extends BVKind
  object i49 extends BVKind
  object i50 extends BVKind
  object i51 extends BVKind
  object i52 extends BVKind
  object i53 extends BVKind
  object i54 extends BVKind
  object i55 extends BVKind
  object i56 extends BVKind
  object i57 extends BVKind
  object i58 extends BVKind
  object i59 extends BVKind
  object i60 extends BVKind
  object i61 extends BVKind
  object i62 extends BVKind
  object i63 extends BVKind
  object i64 extends BVKind
  object i65 extends BVKind
  object i66 extends BVKind
  object i67 extends BVKind
  object i68 extends BVKind
  object i69 extends BVKind
  object i70 extends BVKind
  object i71 extends BVKind
  object i72 extends BVKind
  object i73 extends BVKind
  object i74 extends BVKind
  object i75 extends BVKind
  object i76 extends BVKind
  object i77 extends BVKind
  object i78 extends BVKind
  object i79 extends BVKind
  object i80 extends BVKind
  object i81 extends BVKind
  object i82 extends BVKind
  object i83 extends BVKind
  object i84 extends BVKind
  object i85 extends BVKind
  object i86 extends BVKind
  object i87 extends BVKind
  object i88 extends BVKind
  object i89 extends BVKind
  object i90 extends BVKind
  object i91 extends BVKind
  object i92 extends BVKind
  object i93 extends BVKind
  object i94 extends BVKind
  object i95 extends BVKind
  object i96 extends BVKind
  object i97 extends BVKind
  object i98 extends BVKind
  object i99 extends BVKind
  object i100 extends BVKind
  object i101 extends BVKind
  object i102 extends BVKind
  object i103 extends BVKind
  object i104 extends BVKind
  object i105 extends BVKind
  object i106 extends BVKind
  object i107 extends BVKind
  object i108 extends BVKind
  object i109 extends BVKind
  object i110 extends BVKind
  object i111 extends BVKind
  object i112 extends BVKind
  object i113 extends BVKind
  object i114 extends BVKind
  object i115 extends BVKind
  object i116 extends BVKind
  object i117 extends BVKind
  object i118 extends BVKind
  object i119 extends BVKind
  object i120 extends BVKind
  object i121 extends BVKind
  object i122 extends BVKind
  object i123 extends BVKind
  object i124 extends BVKind
  object i125 extends BVKind
  object i126 extends BVKind
  object i127 extends BVKind
  object i128 extends BVKind
  object i129 extends BVKind
  object i130 extends BVKind
  object i131 extends BVKind
  object i132 extends BVKind
  object i133 extends BVKind
  object i134 extends BVKind
  object i135 extends BVKind
  object i136 extends BVKind
  object i137 extends BVKind
  object i138 extends BVKind
  object i139 extends BVKind
  object i140 extends BVKind
  object i141 extends BVKind
  object i142 extends BVKind
  object i143 extends BVKind
  object i144 extends BVKind
  object i145 extends BVKind
  object i146 extends BVKind
  object i147 extends BVKind
  object i148 extends BVKind
  object i149 extends BVKind
  object i150 extends BVKind
  object i151 extends BVKind
  object i152 extends BVKind
  object i153 extends BVKind
  object i154 extends BVKind
  object i155 extends BVKind
  object i156 extends BVKind
  object i157 extends BVKind
  object i158 extends BVKind
  object i159 extends BVKind
  object i160 extends BVKind
  object i161 extends BVKind
  object i162 extends BVKind
  object i163 extends BVKind
  object i164 extends BVKind
  object i165 extends BVKind
  object i166 extends BVKind
  object i167 extends BVKind
  object i168 extends BVKind
  object i169 extends BVKind
  object i170 extends BVKind
  object i171 extends BVKind
  object i172 extends BVKind
  object i173 extends BVKind
  object i174 extends BVKind
  object i175 extends BVKind
  object i176 extends BVKind
  object i177 extends BVKind
  object i178 extends BVKind
  object i179 extends BVKind
  object i180 extends BVKind
  object i181 extends BVKind
  object i182 extends BVKind
  object i183 extends BVKind
  object i184 extends BVKind
  object i185 extends BVKind
  object i186 extends BVKind
  object i187 extends BVKind
  object i188 extends BVKind
  object i189 extends BVKind
  object i190 extends BVKind
  object i191 extends BVKind
  object i192 extends BVKind
  object i193 extends BVKind
  object i194 extends BVKind
  object i195 extends BVKind
  object i196 extends BVKind
  object i197 extends BVKind
  object i198 extends BVKind
  object i199 extends BVKind
  object i200 extends BVKind
  object i201 extends BVKind
  object i202 extends BVKind
  object i203 extends BVKind
  object i204 extends BVKind
  object i205 extends BVKind
  object i206 extends BVKind
  object i207 extends BVKind
  object i208 extends BVKind
  object i209 extends BVKind
  object i210 extends BVKind
  object i211 extends BVKind
  object i212 extends BVKind
  object i213 extends BVKind
  object i214 extends BVKind
  object i215 extends BVKind
  object i216 extends BVKind
  object i217 extends BVKind
  object i218 extends BVKind
  object i219 extends BVKind
  object i220 extends BVKind
  object i221 extends BVKind
  object i222 extends BVKind
  object i223 extends BVKind
  object i224 extends BVKind
  object i225 extends BVKind
  object i226 extends BVKind
  object i227 extends BVKind
  object i228 extends BVKind
  object i229 extends BVKind
  object i230 extends BVKind
  object i231 extends BVKind
  object i232 extends BVKind
  object i233 extends BVKind
  object i234 extends BVKind
  object i235 extends BVKind
  object i236 extends BVKind
  object i237 extends BVKind
  object i238 extends BVKind
  object i239 extends BVKind
  object i240 extends BVKind
  object i241 extends BVKind
  object i242 extends BVKind
  object i243 extends BVKind
  object i244 extends BVKind
  object i245 extends BVKind
  object i246 extends BVKind
  object i247 extends BVKind
  object i248 extends BVKind
  object i249 extends BVKind
  object i250 extends BVKind
  object i251 extends BVKind
  object i252 extends BVKind
  object i253 extends BVKind
  object i254 extends BVKind
  object i255 extends BVKind
  object i256 extends BVKind

  object u1 extends BVKind
  object u2 extends BVKind
  object u3 extends BVKind
  object u4 extends BVKind
  object u5 extends BVKind
  object u6 extends BVKind
  object u7 extends BVKind
  object u8 extends BVKind
  object u9 extends BVKind
  object u10 extends BVKind
  object u11 extends BVKind
  object u12 extends BVKind
  object u13 extends BVKind
  object u14 extends BVKind
  object u15 extends BVKind
  object u16 extends BVKind
  object u17 extends BVKind
  object u18 extends BVKind
  object u19 extends BVKind
  object u20 extends BVKind
  object u21 extends BVKind
  object u22 extends BVKind
  object u23 extends BVKind
  object u24 extends BVKind
  object u25 extends BVKind
  object u26 extends BVKind
  object u27 extends BVKind
  object u28 extends BVKind
  object u29 extends BVKind
  object u30 extends BVKind
  object u31 extends BVKind
  object u32 extends BVKind
  object u33 extends BVKind
  object u34 extends BVKind
  object u35 extends BVKind
  object u36 extends BVKind
  object u37 extends BVKind
  object u38 extends BVKind
  object u39 extends BVKind
  object u40 extends BVKind
  object u41 extends BVKind
  object u42 extends BVKind
  object u43 extends BVKind
  object u44 extends BVKind
  object u45 extends BVKind
  object u46 extends BVKind
  object u47 extends BVKind
  object u48 extends BVKind
  object u49 extends BVKind
  object u50 extends BVKind
  object u51 extends BVKind
  object u52 extends BVKind
  object u53 extends BVKind
  object u54 extends BVKind
  object u55 extends BVKind
  object u56 extends BVKind
  object u57 extends BVKind
  object u58 extends BVKind
  object u59 extends BVKind
  object u60 extends BVKind
  object u61 extends BVKind
  object u62 extends BVKind
  object u63 extends BVKind
  object u64 extends BVKind
  object u65 extends BVKind
  object u66 extends BVKind
  object u67 extends BVKind
  object u68 extends BVKind
  object u69 extends BVKind
  object u70 extends BVKind
  object u71 extends BVKind
  object u72 extends BVKind
  object u73 extends BVKind
  object u74 extends BVKind
  object u75 extends BVKind
  object u76 extends BVKind
  object u77 extends BVKind
  object u78 extends BVKind
  object u79 extends BVKind
  object u80 extends BVKind
  object u81 extends BVKind
  object u82 extends BVKind
  object u83 extends BVKind
  object u84 extends BVKind
  object u85 extends BVKind
  object u86 extends BVKind
  object u87 extends BVKind
  object u88 extends BVKind
  object u89 extends BVKind
  object u90 extends BVKind
  object u91 extends BVKind
  object u92 extends BVKind
  object u93 extends BVKind
  object u94 extends BVKind
  object u95 extends BVKind
  object u96 extends BVKind
  object u97 extends BVKind
  object u98 extends BVKind
  object u99 extends BVKind
  object u100 extends BVKind
  object u101 extends BVKind
  object u102 extends BVKind
  object u103 extends BVKind
  object u104 extends BVKind
  object u105 extends BVKind
  object u106 extends BVKind
  object u107 extends BVKind
  object u108 extends BVKind
  object u109 extends BVKind
  object u110 extends BVKind
  object u111 extends BVKind
  object u112 extends BVKind
  object u113 extends BVKind
  object u114 extends BVKind
  object u115 extends BVKind
  object u116 extends BVKind
  object u117 extends BVKind
  object u118 extends BVKind
  object u119 extends BVKind
  object u120 extends BVKind
  object u121 extends BVKind
  object u122 extends BVKind
  object u123 extends BVKind
  object u124 extends BVKind
  object u125 extends BVKind
  object u126 extends BVKind
  object u127 extends BVKind
  object u128 extends BVKind
  object u129 extends BVKind
  object u130 extends BVKind
  object u131 extends BVKind
  object u132 extends BVKind
  object u133 extends BVKind
  object u134 extends BVKind
  object u135 extends BVKind
  object u136 extends BVKind
  object u137 extends BVKind
  object u138 extends BVKind
  object u139 extends BVKind
  object u140 extends BVKind
  object u141 extends BVKind
  object u142 extends BVKind
  object u143 extends BVKind
  object u144 extends BVKind
  object u145 extends BVKind
  object u146 extends BVKind
  object u147 extends BVKind
  object u148 extends BVKind
  object u149 extends BVKind
  object u150 extends BVKind
  object u151 extends BVKind
  object u152 extends BVKind
  object u153 extends BVKind
  object u154 extends BVKind
  object u155 extends BVKind
  object u156 extends BVKind
  object u157 extends BVKind
  object u158 extends BVKind
  object u159 extends BVKind
  object u160 extends BVKind
  object u161 extends BVKind
  object u162 extends BVKind
  object u163 extends BVKind
  object u164 extends BVKind
  object u165 extends BVKind
  object u166 extends BVKind
  object u167 extends BVKind
  object u168 extends BVKind
  object u169 extends BVKind
  object u170 extends BVKind
  object u171 extends BVKind
  object u172 extends BVKind
  object u173 extends BVKind
  object u174 extends BVKind
  object u175 extends BVKind
  object u176 extends BVKind
  object u177 extends BVKind
  object u178 extends BVKind
  object u179 extends BVKind
  object u180 extends BVKind
  object u181 extends BVKind
  object u182 extends BVKind
  object u183 extends BVKind
  object u184 extends BVKind
  object u185 extends BVKind
  object u186 extends BVKind
  object u187 extends BVKind
  object u188 extends BVKind
  object u189 extends BVKind
  object u190 extends BVKind
  object u191 extends BVKind
  object u192 extends BVKind
  object u193 extends BVKind
  object u194 extends BVKind
  object u195 extends BVKind
  object u196 extends BVKind
  object u197 extends BVKind
  object u198 extends BVKind
  object u199 extends BVKind
  object u200 extends BVKind
  object u201 extends BVKind
  object u202 extends BVKind
  object u203 extends BVKind
  object u204 extends BVKind
  object u205 extends BVKind
  object u206 extends BVKind
  object u207 extends BVKind
  object u208 extends BVKind
  object u209 extends BVKind
  object u210 extends BVKind
  object u211 extends BVKind
  object u212 extends BVKind
  object u213 extends BVKind
  object u214 extends BVKind
  object u215 extends BVKind
  object u216 extends BVKind
  object u217 extends BVKind
  object u218 extends BVKind
  object u219 extends BVKind
  object u220 extends BVKind
  object u221 extends BVKind
  object u222 extends BVKind
  object u223 extends BVKind
  object u224 extends BVKind
  object u225 extends BVKind
  object u226 extends BVKind
  object u227 extends BVKind
  object u228 extends BVKind
  object u229 extends BVKind
  object u230 extends BVKind
  object u231 extends BVKind
  object u232 extends BVKind
  object u233 extends BVKind
  object u234 extends BVKind
  object u235 extends BVKind
  object u236 extends BVKind
  object u237 extends BVKind
  object u238 extends BVKind
  object u239 extends BVKind
  object u240 extends BVKind
  object u241 extends BVKind
  object u242 extends BVKind
  object u243 extends BVKind
  object u244 extends BVKind
  object u245 extends BVKind
  object u246 extends BVKind
  object u247 extends BVKind
  object u248 extends BVKind
  object u249 extends BVKind
  object u250 extends BVKind
  object u251 extends BVKind
  object u252 extends BVKind
  object u253 extends BVKind
  object u254 extends BVKind
  object u255 extends BVKind
  object u256 extends BVKind

  type Int1 = BV[i1.type]
  type Int2 = BV[i2.type]
  type Int3 = BV[i3.type]
  type Int4 = BV[i4.type]
  type Int5 = BV[i5.type]
  type Int6 = BV[i6.type]
  type Int7 = BV[i7.type]
  type Int8 = BV[i8.type]
  type Int9 = BV[i9.type]
  type Int10 = BV[i10.type]
  type Int11 = BV[i11.type]
  type Int12 = BV[i12.type]
  type Int13 = BV[i13.type]
  type Int14 = BV[i14.type]
  type Int15 = BV[i15.type]
  type Int16 = BV[i16.type]
  type Int17 = BV[i17.type]
  type Int18 = BV[i18.type]
  type Int19 = BV[i19.type]
  type Int20 = BV[i20.type]
  type Int21 = BV[i21.type]
  type Int22 = BV[i22.type]
  type Int23 = BV[i23.type]
  type Int24 = BV[i24.type]
  type Int25 = BV[i25.type]
  type Int26 = BV[i26.type]
  type Int27 = BV[i27.type]
  type Int28 = BV[i28.type]
  type Int29 = BV[i29.type]
  type Int30 = BV[i30.type]
  type Int31 = BV[i31.type]
  type Int32 = BV[i32.type]
  type Int33 = BV[i33.type]
  type Int34 = BV[i34.type]
  type Int35 = BV[i35.type]
  type Int36 = BV[i36.type]
  type Int37 = BV[i37.type]
  type Int38 = BV[i38.type]
  type Int39 = BV[i39.type]
  type Int40 = BV[i40.type]
  type Int41 = BV[i41.type]
  type Int42 = BV[i42.type]
  type Int43 = BV[i43.type]
  type Int44 = BV[i44.type]
  type Int45 = BV[i45.type]
  type Int46 = BV[i46.type]
  type Int47 = BV[i47.type]
  type Int48 = BV[i48.type]
  type Int49 = BV[i49.type]
  type Int50 = BV[i50.type]
  type Int51 = BV[i51.type]
  type Int52 = BV[i52.type]
  type Int53 = BV[i53.type]
  type Int54 = BV[i54.type]
  type Int55 = BV[i55.type]
  type Int56 = BV[i56.type]
  type Int57 = BV[i57.type]
  type Int58 = BV[i58.type]
  type Int59 = BV[i59.type]
  type Int60 = BV[i60.type]
  type Int61 = BV[i61.type]
  type Int62 = BV[i62.type]
  type Int63 = BV[i63.type]
  type Int64 = BV[i64.type]
  type Int65 = BV[i65.type]
  type Int66 = BV[i66.type]
  type Int67 = BV[i67.type]
  type Int68 = BV[i68.type]
  type Int69 = BV[i69.type]
  type Int70 = BV[i70.type]
  type Int71 = BV[i71.type]
  type Int72 = BV[i72.type]
  type Int73 = BV[i73.type]
  type Int74 = BV[i74.type]
  type Int75 = BV[i75.type]
  type Int76 = BV[i76.type]
  type Int77 = BV[i77.type]
  type Int78 = BV[i78.type]
  type Int79 = BV[i79.type]
  type Int80 = BV[i80.type]
  type Int81 = BV[i81.type]
  type Int82 = BV[i82.type]
  type Int83 = BV[i83.type]
  type Int84 = BV[i84.type]
  type Int85 = BV[i85.type]
  type Int86 = BV[i86.type]
  type Int87 = BV[i87.type]
  type Int88 = BV[i88.type]
  type Int89 = BV[i89.type]
  type Int90 = BV[i90.type]
  type Int91 = BV[i91.type]
  type Int92 = BV[i92.type]
  type Int93 = BV[i93.type]
  type Int94 = BV[i94.type]
  type Int95 = BV[i95.type]
  type Int96 = BV[i96.type]
  type Int97 = BV[i97.type]
  type Int98 = BV[i98.type]
  type Int99 = BV[i99.type]
  type Int100 = BV[i100.type]
  type Int101 = BV[i101.type]
  type Int102 = BV[i102.type]
  type Int103 = BV[i103.type]
  type Int104 = BV[i104.type]
  type Int105 = BV[i105.type]
  type Int106 = BV[i106.type]
  type Int107 = BV[i107.type]
  type Int108 = BV[i108.type]
  type Int109 = BV[i109.type]
  type Int110 = BV[i110.type]
  type Int111 = BV[i111.type]
  type Int112 = BV[i112.type]
  type Int113 = BV[i113.type]
  type Int114 = BV[i114.type]
  type Int115 = BV[i115.type]
  type Int116 = BV[i116.type]
  type Int117 = BV[i117.type]
  type Int118 = BV[i118.type]
  type Int119 = BV[i119.type]
  type Int120 = BV[i120.type]
  type Int121 = BV[i121.type]
  type Int122 = BV[i122.type]
  type Int123 = BV[i123.type]
  type Int124 = BV[i124.type]
  type Int125 = BV[i125.type]
  type Int126 = BV[i126.type]
  type Int127 = BV[i127.type]
  type Int128 = BV[i128.type]
  type Int129 = BV[i129.type]
  type Int130 = BV[i130.type]
  type Int131 = BV[i131.type]
  type Int132 = BV[i132.type]
  type Int133 = BV[i133.type]
  type Int134 = BV[i134.type]
  type Int135 = BV[i135.type]
  type Int136 = BV[i136.type]
  type Int137 = BV[i137.type]
  type Int138 = BV[i138.type]
  type Int139 = BV[i139.type]
  type Int140 = BV[i140.type]
  type Int141 = BV[i141.type]
  type Int142 = BV[i142.type]
  type Int143 = BV[i143.type]
  type Int144 = BV[i144.type]
  type Int145 = BV[i145.type]
  type Int146 = BV[i146.type]
  type Int147 = BV[i147.type]
  type Int148 = BV[i148.type]
  type Int149 = BV[i149.type]
  type Int150 = BV[i150.type]
  type Int151 = BV[i151.type]
  type Int152 = BV[i152.type]
  type Int153 = BV[i153.type]
  type Int154 = BV[i154.type]
  type Int155 = BV[i155.type]
  type Int156 = BV[i156.type]
  type Int157 = BV[i157.type]
  type Int158 = BV[i158.type]
  type Int159 = BV[i159.type]
  type Int160 = BV[i160.type]
  type Int161 = BV[i161.type]
  type Int162 = BV[i162.type]
  type Int163 = BV[i163.type]
  type Int164 = BV[i164.type]
  type Int165 = BV[i165.type]
  type Int166 = BV[i166.type]
  type Int167 = BV[i167.type]
  type Int168 = BV[i168.type]
  type Int169 = BV[i169.type]
  type Int170 = BV[i170.type]
  type Int171 = BV[i171.type]
  type Int172 = BV[i172.type]
  type Int173 = BV[i173.type]
  type Int174 = BV[i174.type]
  type Int175 = BV[i175.type]
  type Int176 = BV[i176.type]
  type Int177 = BV[i177.type]
  type Int178 = BV[i178.type]
  type Int179 = BV[i179.type]
  type Int180 = BV[i180.type]
  type Int181 = BV[i181.type]
  type Int182 = BV[i182.type]
  type Int183 = BV[i183.type]
  type Int184 = BV[i184.type]
  type Int185 = BV[i185.type]
  type Int186 = BV[i186.type]
  type Int187 = BV[i187.type]
  type Int188 = BV[i188.type]
  type Int189 = BV[i189.type]
  type Int190 = BV[i190.type]
  type Int191 = BV[i191.type]
  type Int192 = BV[i192.type]
  type Int193 = BV[i193.type]
  type Int194 = BV[i194.type]
  type Int195 = BV[i195.type]
  type Int196 = BV[i196.type]
  type Int197 = BV[i197.type]
  type Int198 = BV[i198.type]
  type Int199 = BV[i199.type]
  type Int200 = BV[i200.type]
  type Int201 = BV[i201.type]
  type Int202 = BV[i202.type]
  type Int203 = BV[i203.type]
  type Int204 = BV[i204.type]
  type Int205 = BV[i205.type]
  type Int206 = BV[i206.type]
  type Int207 = BV[i207.type]
  type Int208 = BV[i208.type]
  type Int209 = BV[i209.type]
  type Int210 = BV[i210.type]
  type Int211 = BV[i211.type]
  type Int212 = BV[i212.type]
  type Int213 = BV[i213.type]
  type Int214 = BV[i214.type]
  type Int215 = BV[i215.type]
  type Int216 = BV[i216.type]
  type Int217 = BV[i217.type]
  type Int218 = BV[i218.type]
  type Int219 = BV[i219.type]
  type Int220 = BV[i220.type]
  type Int221 = BV[i221.type]
  type Int222 = BV[i222.type]
  type Int223 = BV[i223.type]
  type Int224 = BV[i224.type]
  type Int225 = BV[i225.type]
  type Int226 = BV[i226.type]
  type Int227 = BV[i227.type]
  type Int228 = BV[i228.type]
  type Int229 = BV[i229.type]
  type Int230 = BV[i230.type]
  type Int231 = BV[i231.type]
  type Int232 = BV[i232.type]
  type Int233 = BV[i233.type]
  type Int234 = BV[i234.type]
  type Int235 = BV[i235.type]
  type Int236 = BV[i236.type]
  type Int237 = BV[i237.type]
  type Int238 = BV[i238.type]
  type Int239 = BV[i239.type]
  type Int240 = BV[i240.type]
  type Int241 = BV[i241.type]
  type Int242 = BV[i242.type]
  type Int243 = BV[i243.type]
  type Int244 = BV[i244.type]
  type Int245 = BV[i245.type]
  type Int246 = BV[i246.type]
  type Int247 = BV[i247.type]
  type Int248 = BV[i248.type]
  type Int249 = BV[i249.type]
  type Int250 = BV[i250.type]
  type Int251 = BV[i251.type]
  type Int252 = BV[i252.type]
  type Int253 = BV[i253.type]
  type Int254 = BV[i254.type]
  type Int255 = BV[i255.type]
  type Int256 = BV[i256.type]

  type UInt1 = BV[u1.type]
  type UInt2 = BV[u2.type]
  type UInt3 = BV[u3.type]
  type UInt4 = BV[u4.type]
  type UInt5 = BV[u5.type]
  type UInt6 = BV[u6.type]
  type UInt7 = BV[u7.type]
  type UInt8 = BV[u8.type]
  type UInt9 = BV[u9.type]
  type UInt10 = BV[u10.type]
  type UInt11 = BV[u11.type]
  type UInt12 = BV[u12.type]
  type UInt13 = BV[u13.type]
  type UInt14 = BV[u14.type]
  type UInt15 = BV[u15.type]
  type UInt16 = BV[u16.type]
  type UInt17 = BV[u17.type]
  type UInt18 = BV[u18.type]
  type UInt19 = BV[u19.type]
  type UInt20 = BV[u20.type]
  type UInt21 = BV[u21.type]
  type UInt22 = BV[u22.type]
  type UInt23 = BV[u23.type]
  type UInt24 = BV[u24.type]
  type UInt25 = BV[u25.type]
  type UInt26 = BV[u26.type]
  type UInt27 = BV[u27.type]
  type UInt28 = BV[u28.type]
  type UInt29 = BV[u29.type]
  type UInt30 = BV[u30.type]
  type UInt31 = BV[u31.type]
  type UInt32 = BV[u32.type]
  type UInt33 = BV[u33.type]
  type UInt34 = BV[u34.type]
  type UInt35 = BV[u35.type]
  type UInt36 = BV[u36.type]
  type UInt37 = BV[u37.type]
  type UInt38 = BV[u38.type]
  type UInt39 = BV[u39.type]
  type UInt40 = BV[u40.type]
  type UInt41 = BV[u41.type]
  type UInt42 = BV[u42.type]
  type UInt43 = BV[u43.type]
  type UInt44 = BV[u44.type]
  type UInt45 = BV[u45.type]
  type UInt46 = BV[u46.type]
  type UInt47 = BV[u47.type]
  type UInt48 = BV[u48.type]
  type UInt49 = BV[u49.type]
  type UInt50 = BV[u50.type]
  type UInt51 = BV[u51.type]
  type UInt52 = BV[u52.type]
  type UInt53 = BV[u53.type]
  type UInt54 = BV[u54.type]
  type UInt55 = BV[u55.type]
  type UInt56 = BV[u56.type]
  type UInt57 = BV[u57.type]
  type UInt58 = BV[u58.type]
  type UInt59 = BV[u59.type]
  type UInt60 = BV[u60.type]
  type UInt61 = BV[u61.type]
  type UInt62 = BV[u62.type]
  type UInt63 = BV[u63.type]
  type UInt64 = BV[u64.type]
  type UInt65 = BV[u65.type]
  type UInt66 = BV[u66.type]
  type UInt67 = BV[u67.type]
  type UInt68 = BV[u68.type]
  type UInt69 = BV[u69.type]
  type UInt70 = BV[u70.type]
  type UInt71 = BV[u71.type]
  type UInt72 = BV[u72.type]
  type UInt73 = BV[u73.type]
  type UInt74 = BV[u74.type]
  type UInt75 = BV[u75.type]
  type UInt76 = BV[u76.type]
  type UInt77 = BV[u77.type]
  type UInt78 = BV[u78.type]
  type UInt79 = BV[u79.type]
  type UInt80 = BV[u80.type]
  type UInt81 = BV[u81.type]
  type UInt82 = BV[u82.type]
  type UInt83 = BV[u83.type]
  type UInt84 = BV[u84.type]
  type UInt85 = BV[u85.type]
  type UInt86 = BV[u86.type]
  type UInt87 = BV[u87.type]
  type UInt88 = BV[u88.type]
  type UInt89 = BV[u89.type]
  type UInt90 = BV[u90.type]
  type UInt91 = BV[u91.type]
  type UInt92 = BV[u92.type]
  type UInt93 = BV[u93.type]
  type UInt94 = BV[u94.type]
  type UInt95 = BV[u95.type]
  type UInt96 = BV[u96.type]
  type UInt97 = BV[u97.type]
  type UInt98 = BV[u98.type]
  type UInt99 = BV[u99.type]
  type UInt100 = BV[u100.type]
  type UInt101 = BV[u101.type]
  type UInt102 = BV[u102.type]
  type UInt103 = BV[u103.type]
  type UInt104 = BV[u104.type]
  type UInt105 = BV[u105.type]
  type UInt106 = BV[u106.type]
  type UInt107 = BV[u107.type]
  type UInt108 = BV[u108.type]
  type UInt109 = BV[u109.type]
  type UInt110 = BV[u110.type]
  type UInt111 = BV[u111.type]
  type UInt112 = BV[u112.type]
  type UInt113 = BV[u113.type]
  type UInt114 = BV[u114.type]
  type UInt115 = BV[u115.type]
  type UInt116 = BV[u116.type]
  type UInt117 = BV[u117.type]
  type UInt118 = BV[u118.type]
  type UInt119 = BV[u119.type]
  type UInt120 = BV[u120.type]
  type UInt121 = BV[u121.type]
  type UInt122 = BV[u122.type]
  type UInt123 = BV[u123.type]
  type UInt124 = BV[u124.type]
  type UInt125 = BV[u125.type]
  type UInt126 = BV[u126.type]
  type UInt127 = BV[u127.type]
  type UInt128 = BV[u128.type]
  type UInt129 = BV[u129.type]
  type UInt130 = BV[u130.type]
  type UInt131 = BV[u131.type]
  type UInt132 = BV[u132.type]
  type UInt133 = BV[u133.type]
  type UInt134 = BV[u134.type]
  type UInt135 = BV[u135.type]
  type UInt136 = BV[u136.type]
  type UInt137 = BV[u137.type]
  type UInt138 = BV[u138.type]
  type UInt139 = BV[u139.type]
  type UInt140 = BV[u140.type]
  type UInt141 = BV[u141.type]
  type UInt142 = BV[u142.type]
  type UInt143 = BV[u143.type]
  type UInt144 = BV[u144.type]
  type UInt145 = BV[u145.type]
  type UInt146 = BV[u146.type]
  type UInt147 = BV[u147.type]
  type UInt148 = BV[u148.type]
  type UInt149 = BV[u149.type]
  type UInt150 = BV[u150.type]
  type UInt151 = BV[u151.type]
  type UInt152 = BV[u152.type]
  type UInt153 = BV[u153.type]
  type UInt154 = BV[u154.type]
  type UInt155 = BV[u155.type]
  type UInt156 = BV[u156.type]
  type UInt157 = BV[u157.type]
  type UInt158 = BV[u158.type]
  type UInt159 = BV[u159.type]
  type UInt160 = BV[u160.type]
  type UInt161 = BV[u161.type]
  type UInt162 = BV[u162.type]
  type UInt163 = BV[u163.type]
  type UInt164 = BV[u164.type]
  type UInt165 = BV[u165.type]
  type UInt166 = BV[u166.type]
  type UInt167 = BV[u167.type]
  type UInt168 = BV[u168.type]
  type UInt169 = BV[u169.type]
  type UInt170 = BV[u170.type]
  type UInt171 = BV[u171.type]
  type UInt172 = BV[u172.type]
  type UInt173 = BV[u173.type]
  type UInt174 = BV[u174.type]
  type UInt175 = BV[u175.type]
  type UInt176 = BV[u176.type]
  type UInt177 = BV[u177.type]
  type UInt178 = BV[u178.type]
  type UInt179 = BV[u179.type]
  type UInt180 = BV[u180.type]
  type UInt181 = BV[u181.type]
  type UInt182 = BV[u182.type]
  type UInt183 = BV[u183.type]
  type UInt184 = BV[u184.type]
  type UInt185 = BV[u185.type]
  type UInt186 = BV[u186.type]
  type UInt187 = BV[u187.type]
  type UInt188 = BV[u188.type]
  type UInt189 = BV[u189.type]
  type UInt190 = BV[u190.type]
  type UInt191 = BV[u191.type]
  type UInt192 = BV[u192.type]
  type UInt193 = BV[u193.type]
  type UInt194 = BV[u194.type]
  type UInt195 = BV[u195.type]
  type UInt196 = BV[u196.type]
  type UInt197 = BV[u197.type]
  type UInt198 = BV[u198.type]
  type UInt199 = BV[u199.type]
  type UInt200 = BV[u200.type]
  type UInt201 = BV[u201.type]
  type UInt202 = BV[u202.type]
  type UInt203 = BV[u203.type]
  type UInt204 = BV[u204.type]
  type UInt205 = BV[u205.type]
  type UInt206 = BV[u206.type]
  type UInt207 = BV[u207.type]
  type UInt208 = BV[u208.type]
  type UInt209 = BV[u209.type]
  type UInt210 = BV[u210.type]
  type UInt211 = BV[u211.type]
  type UInt212 = BV[u212.type]
  type UInt213 = BV[u213.type]
  type UInt214 = BV[u214.type]
  type UInt215 = BV[u215.type]
  type UInt216 = BV[u216.type]
  type UInt217 = BV[u217.type]
  type UInt218 = BV[u218.type]
  type UInt219 = BV[u219.type]
  type UInt220 = BV[u220.type]
  type UInt221 = BV[u221.type]
  type UInt222 = BV[u222.type]
  type UInt223 = BV[u223.type]
  type UInt224 = BV[u224.type]
  type UInt225 = BV[u225.type]
  type UInt226 = BV[u226.type]
  type UInt227 = BV[u227.type]
  type UInt228 = BV[u228.type]
  type UInt229 = BV[u229.type]
  type UInt230 = BV[u230.type]
  type UInt231 = BV[u231.type]
  type UInt232 = BV[u232.type]
  type UInt233 = BV[u233.type]
  type UInt234 = BV[u234.type]
  type UInt235 = BV[u235.type]
  type UInt236 = BV[u236.type]
  type UInt237 = BV[u237.type]
  type UInt238 = BV[u238.type]
  type UInt239 = BV[u239.type]
  type UInt240 = BV[u240.type]
  type UInt241 = BV[u241.type]
  type UInt242 = BV[u242.type]
  type UInt243 = BV[u243.type]
  type UInt244 = BV[u244.type]
  type UInt245 = BV[u245.type]
  type UInt246 = BV[u246.type]
  type UInt247 = BV[u247.type]
  type UInt248 = BV[u248.type]
  type UInt249 = BV[u249.type]
  type UInt250 = BV[u250.type]
  type UInt251 = BV[u251.type]
  type UInt252 = BV[u252.type]
  type UInt253 = BV[u253.type]
  type UInt254 = BV[u254.type]
  type UInt255 = BV[u255.type]
  type UInt256 = BV[u256.type]

  implicit def intToBV[T <: BVKind with Singleton](i: Int): BV[T] = ???
  implicit def bigIntToBV[T <: BVKind with Singleton](i: BigInt): BV[T] = ???

  implicit class ArrayIndexing[T](underlying: Array[T]) {
    def apply[X <: BVKind with Singleton](bv: BV[X]): T = underlying(bv.toInt)
  }

  def min[X <: BV[_ <: BVKind with Singleton]]: X = ???
  def max[X <: BV[_ <: BVKind with Singleton]]: X = ???

  def fromByte(n: Byte): Int8 = ???
  def fromShort(n: Short): Int16 = ???
  def fromInt(n: Int): Int32 = ???
  def fromLong(n: Long): Int64 = ???

  case class BV[T <: BVKind with Singleton](underlying: BitSet) {

    def unary_- :           BV[T]   = { ??? }
    def +(other: BV[T]):    BV[T]   = { ??? }
    def -(other: BV[T]):    BV[T]   = { ??? }
    def *(other: BV[T]):    BV[T]   = { ??? }
    def %(other: BV[T]):    BV[T]   = { ??? }
    def mod(other: BV[T]):  BV[T]   = { ??? }
    def /(other: BV[T]):    BV[T]   = { ??? }
    def >(other: BV[T]):    Boolean = { ??? }
    def >=(other: BV[T]):   Boolean = { ??? }
    def <(other: BV[T]):    Boolean = { ??? }
    def <=(other: BV[T]):   Boolean = { ??? }
    def |(other: BV[T]):    BV[T]   = { ??? }
    def &(other: BV[T]):    BV[T]   = { ??? }
    def ^(other: BV[T]):    BV[T]   = { ??? }
    def <<(other: BV[T]):   BV[T]   = { ??? }
    def >>(other: BV[T]):   BV[T]   = { ??? }
    def >>>(other: BV[T]):  BV[T]   = { ??? }

    def widen [X <: BV[_ <: BVKind with Singleton]]: X = { ??? }
    def narrow[X <: BV[_ <: BVKind with Singleton]]: X = { ??? }
    def toSigned[X <: BV[_ <: BVKind with Singleton]]: X = { ??? }
    def toUnsigned[X <: BV[_ <: BVKind with Singleton]]: X = { ??? }

    def toByte: Byte = { ??? }
    def toShort: Short = { ??? }
    def toInt: Int = { ??? }
    def toLong: Long = { ??? }
  }

}
