const EmptyTag = "";
const EmptyTree = null;
const EmptyState = null;

class clink {
  constructor(tag,child,prev) {
    this.tag = tag;
    this.child = child;
    this.prev = prev;
  }
  toString() {
    if(this.child != null && this.tag != null){
      return '$' + this.tag + '=' + this.child.toString();
    }
    return '';
  }
  getTag() {
     for (var cur = this; cur != null; cur = cur.prev) {
        if (cur.child == null) {
           return cur.tag;
        }
     }
     return EmptyTag;
  }
}

class ctree {
  constructor(tag,inputs,spos,epos,child) {
    this.tag = (tag == EmptyTag && child != null) ? child.getTag() : tag;
    this.inputs = inputs;
    this.spos = spos;
    this.epos = epos;
    this.child = child;
  }
  toString() {
    var s = "[#" + this.tag;
    var cur = this.child;
    var cnt = 0;
    while(cur != null){
      s = s + " " + cur.toString();
      cur = cur.prev;
      cnt++;
    }
    if(cnt == 1){
      s = s + " '" + this.inputs.slice(this.spos, this.epos).toString() + "'";
    }
    return s + "]";
  }
}

class cmemo {
  constructor() {
    this.key = 0;
    this.matched = false;
    this.mpos = 0;
    this.mtree = null;
    this.mstate = null;
  }
}

class cstate {
  constructor(ns, spos, epos, sprev) {
    this.ns = ns;
    this.spos = spos;
    this.slen = epos - spos;
    this.sprev = sprev;
  }
}

class ParserContext {
  constructor(inputs, length, memolen) {
    this.inputs = inputs;
    this.length = length;
    this.pos = 0;
    this.headpos = 0;
    this.tree = null;
    this.state = null;
    this.memos = [...Array(memolen).keys()].map(function(){return new cmemo()});
  }
}

function bits32(bits, b){
  var n = b & 0xff;
  return (bits[n / 32 | 0] & (1 << (n % 32))) != 0;
}

function mbackpos(px, pos){
  if(px.headpos < px.pos){
    px.headpos = px.pos;
  }
  return pos;
}

const memosize = 0
const memolen = 1
const bs0 = [9728,1,0,0,0,0,0,0]
const bs1 = [0,8192,0,0,0,0,0,0]
const bs2 = [0,128,0,0,0,0,0,0]
const bs3 = [512,1,0,0,0,0,0,0]
const bs4 = [0,0,-2013265922,134217726,-1,-1,-1,16777215]
const bs5 = [0,67043328,-2013265922,134217726,-1,-1,-1,16777215]
const bs6 = [0,0,1048576,1048576,0,0,0,0]
const bs7 = [0,0,64,64,0,0,0,0]
const bs8 = [0,0,16384,16384,0,0,0,0]
const bs9 = [0,2048,0,1073741824,0,0,0,0]
const bs10 = [-1025,-5,-268435457,-1,-1,-1,-1,-1]
const bs11 = [-1025,-129,-268435457,-1,-1,-1,-1,-1]
const bs12 = [-1025,-1342177281,-268435457,-1,-1,-1,-1,-1]
const bs13 = [0,67043328,0,0,0,0,0,0]
const bs14 = [0,67043328,-2130706428,16777220,0,0,0,0]
const bs15 = [0,66977792,0,0,0,0,0,0]
const bs16 = [0,0,-2147483648,0,0,0,0,0]
const bs17 = [0,0,16777216,16777216,0,0,0,0]
const bs18 = [0,67043328,126,126,0,0,0,0]
const bs19 = [0,0,4,4,0,0,0,0]
const bs20 = [0,196608,0,0,0,0,0,0]
const bs21 = [0,132,268435456,1327172,0,0,0,0]
const bs22 = [0,983040,0,0,0,0,0,0]
const bs23 = [0,16711680,0,0,0,0,0,0]
const bs24 = [0,0,0,2097152,0,0,0,0]
const bs25 = [0,0,32,32,0,0,0,0]
const bs26 = [0,10240,0,0,0,0,0,0]
function mnext1(px){
  px.pos = px.pos + 1;
  return true;
}

function mback1(px,pos){
  px.pos = mbackpos(px, pos);
  return true;
}

function mback3(px,pos,tree){
  px.pos = mbackpos(px, pos);
  px.tree = tree;
  return true;
}

function or1(px,pe,pe2){
  var pos = px.pos;
  return pe(px) || mback1(px,pos) && pe2(px);
}

function or3(px,pe,pe2){
  var pos = px.pos;
  var tree = px.tree;
  return pe(px) || mback3(px,pos,tree) && pe2(px);
}

function many1(px,pe){
  var pos = px.pos;
  while(pe(px)) {
    pos = px.pos;
  }
  return mback1(px,pos);
}

function many3(px,pe){
  var pos = px.pos;
  var tree = px.tree;
  while(pe(px)) {
    pos = px.pos;
    tree = px.tree;
  }
  return mback3(px,pos,tree);
}

function manychar(px,bm){
  while(bits32(bm,px.inputs[px.pos])) {
    px.pos = px.pos + 1;
  }
  return true;
}

function not1(px,pe){
  var pos = px.pos;
  return !(pe(px)) && mback1(px,pos);
}

function mtree(px,tag,spos,epos){
  px.tree = new ctree(tag,px.inputs,spos,epos,px.tree);
  return true;
}

function mlink(px,tag,child,prev){
  px.tree = new clink(tag,child,prev);
  return true;
}

function newtree(px,spos,pe,tag,epos){
  var pos = px.pos;
  px.tree = EmptyTree;
  return pe(px) && mtree(px,tag,pos + spos,px.pos + epos);
}

function foldtree(px,spos,label,pe,tag,epos){
  var pos = px.pos;
  return mlink(px,label,px.tree,EmptyTree) && pe(px) && mtree(px,tag,pos + spos,px.pos + epos);
}

function linktree(px,tag,pe){
  var tree = px.tree;
  return pe(px) && mlink(px,tag,px.tree,tree);
}

function tagtree(px,tag){
  return mlink(px,tag,EmptyTree,px.tree);
}

function e80(px){
  return or1(px,(p240) => p240.inputs[p240.pos++] == 92 && bits32(bs21,p240.inputs[p240.pos++]),(p247) => or1(p247,(p241) => p241.inputs[p241.pos++] == 92 && bits32(bs22,p241.inputs[p241.pos++]) && bits32(bs23,p241.inputs[p241.pos++]) && bits32(bs23,p241.inputs[p241.pos++]),(p246) => or1(p246,(p242) => p242.inputs[p242.pos++] == 92 && bits32(bs23,p242.inputs[p242.pos++]) && bits32(bs23,p242.inputs[p242.pos++]),(p245) => or1(p245,(p243) => p243.inputs[p243.pos++] == 92 && bits32(bs23,p243.inputs[p243.pos++]),(p244) => p244.inputs[p244.pos++] == 92 && p244.inputs[p244.pos++] == 117 && manychar(p244,bs24) && bits32(bs18,p244.inputs[p244.pos++]) && bits32(bs18,p244.inputs[p244.pos++]) && bits32(bs18,p244.inputs[p244.pos++]) && bits32(bs18,p244.inputs[p244.pos++])))));
}

function e73(px){
  return or1(px,e80,(p206) => bits32(bs12,p206.inputs[p206.pos++]));
}

function e72(px){
  return or1(px,e80,(p205) => bits32(bs11,p205.inputs[p205.pos++]));
}

function e3(px){
  return !(px.pos < px.length);
}

function e8(px){
  return or1(px,(p23) => or1(p23,(p21) => p21.inputs[p21.pos++] == 13,(p22) => true) && p23.inputs[p23.pos++] == 10,e3);
}

function e5(px){
  return px.inputs[px.pos++] == 47 && px.inputs[px.pos++] == 47 && many1(px,(p15) => not1(p15,e8) && p15.pos < p15.length && mnext1(p15)) && e8(px);
}

function e4(px){
  return or1(px,(p11) => p11.inputs[p11.pos++] == 47 && p11.inputs[p11.pos++] == 42 && many1(p11,(p10) => not1(p10,(p9) => p9.inputs[p9.pos++] == 42 && p9.inputs[p9.pos++] == 47) && p10.pos < p10.length && mnext1(p10)) && p11.inputs[p11.pos++] == 42 && p11.inputs[p11.pos++] == 47,(p14) => p14.inputs[p14.pos++] == 40 && p14.inputs[p14.pos++] == 42 && many1(p14,(p13) => not1(p13,(p12) => p12.inputs[p12.pos++] == 42 && p12.inputs[p12.pos++] == 41) && p13.pos < p13.length && mnext1(p13)) && p14.inputs[p14.pos++] == 42 && p14.inputs[p14.pos++] == 41);
}

function e18(px){
  return many1(px,(p47) => or1(p47,(p45) => bits32(bs3,p45.inputs[p45.pos++]),(p46) => or1(p46,e4,e5)));
}

function e46(px){
  return newtree(px,0,(p130) => or1(p130,(p116) => p116.inputs[p116.pos++] == 61 && p116.inputs[p116.pos++] == 61 && p116.inputs[p116.pos++] == 61,(p129) => or1(p129,(p117) => p117.inputs[p117.pos++] == 61 && p117.inputs[p117.pos++] == 61,(p128) => or1(p128,(p118) => p118.inputs[p118.pos++] == 33 && p118.inputs[p118.pos++] == 61,(p127) => or1(p127,(p119) => p119.inputs[p119.pos++] == 60 && p119.inputs[p119.pos++] == 61,(p126) => or1(p126,(p120) => p120.inputs[p120.pos++] == 62 && p120.inputs[p120.pos++] == 61,(p125) => or1(p125,(p121) => p121.inputs[p121.pos++] == 60,(p124) => or1(p124,(p122) => p122.inputs[p122.pos++] == 62,(p123) => p123.inputs[p123.pos++] == 105 && p123.inputs[p123.pos++] == 110 && !(bits32(bs5,p123.inputs[p123.pos]))))))))) && tagtree(p130,"Name"),EmptyTag,0) && e18(px);
}

function e79(px){
  return newtree(px,0,(p239) => or1(p239,(p223) => p223.inputs[p223.pos++] == 94,(p238) => or1(p238,(p224) => p224.inputs[p224.pos++] == 42 && p224.inputs[p224.pos++] == 42 && !(p224.inputs[p224.pos] == 42),(p237) => or1(p237,(p225) => p225.inputs[p225.pos++] == 60 && p225.inputs[p225.pos++] == 60,(p236) => or1(p236,(p226) => p226.inputs[p226.pos++] == 62 && p226.inputs[p226.pos++] == 62,(p235) => or1(p235,(p227) => p227.inputs[p227.pos++] == 38 && !(p227.inputs[p227.pos] == 38),(p234) => or1(p234,(p228) => p228.inputs[p228.pos++] == 47,(p233) => or1(p233,(p229) => p229.inputs[p229.pos++] == 42,(p232) => or1(p232,(p230) => p230.inputs[p230.pos++] == 37,(p231) => p231.inputs[p231.pos++] == 109 && p231.inputs[p231.pos++] == 111 && p231.inputs[p231.pos++] == 100 && !(bits32(bs5,p231.inputs[p231.pos])))))))))) && tagtree(p239,"Name"),EmptyTag,0) && e18(px);
}

function e66(px){
  return newtree(px,0,(p186) => or1(p186,(p180) => p180.inputs[p180.pos++] == 45,(p185) => or1(p185,(p181) => p181.inputs[p181.pos++] == 33,(p184) => or1(p184,(p182) => p182.inputs[p182.pos++] == 110 && p182.inputs[p182.pos++] == 111 && p182.inputs[p182.pos++] == 116 && bits32(bs3,p182.inputs[p182.pos++]),(p183) => bits32(bs9,p183.inputs[p183.pos++])))),EmptyTag,0) && e18(px);
}

function e30(px){
  return !(bits32(bs5,px.inputs[px.pos])) && e18(px);
}

function e83(px){
  return or1(px,(p256) => p256.inputs[p256.pos++] == 116 && p256.inputs[p256.pos++] == 111 && e30(p256),(p259) => or1(p259,(p257) => p257.inputs[p257.pos++] == 97 && p257.inputs[p257.pos++] == 115 && e30(p257),(p258) => p258.inputs[p258.pos++] == 61 && p258.inputs[p258.pos++] == 62 && e18(p258)));
}

function e33(px){
  return px.inputs[px.pos++] == 102 && px.inputs[px.pos++] == 111 && px.inputs[px.pos++] == 114 && px.inputs[px.pos++] == 101 && px.inputs[px.pos++] == 97 && px.inputs[px.pos++] == 99 && px.inputs[px.pos++] == 104 && !(bits32(bs5,px.inputs[px.pos]));
}

function e34(px){
  return px.inputs[px.pos++] == 119 && px.inputs[px.pos++] == 104 && px.inputs[px.pos++] == 101 && px.inputs[px.pos++] == 110 && !(bits32(bs5,px.inputs[px.pos]));
}

function e22(px){
  return or1(px,e33,e34);
}

function e23(px){
  return bits32(bs4,px.inputs[px.pos++]) && manychar(px,bs5);
}

function e13(px){
  return not1(px,e22) && newtree(px,0,(p41) => e23(p41) && manychar(p41,bs2) && or1(p41,(p39) => p39.inputs[p39.pos++] == 63,(p40) => true) && tagtree(p41,"Name"),EmptyTag,0) && e18(px);
}

function e48(px){
  return px.inputs[px.pos++] == 93 && e18(px);
}

function e47(px){
  return px.inputs[px.pos++] == 91 && e18(px);
}

function e1(px){
  return many1(px,(p5) => or1(p5,(p3) => bits32(bs0,p3.inputs[p3.pos++]),(p4) => or1(p4,e4,e5)));
}

function e17(px){
  return px.inputs[px.pos++] == 44 && e1(px);
}

function e28(px){
  return newtree(px,0,(p71) => or3(p71,(p68) => linktree(p68,"",e15),(p69) => true) && many3(p71,(p70) => e17(p70) && linktree(p70,"",e15)) && tagtree(p71,"Arguments"),EmptyTag,0);
}

function e27(px){
  return px.inputs[px.pos++] == 40 && e18(px);
}

function e29(px){
  return px.inputs[px.pos++] == 41 && e18(px);
}

function e78(px){
  return or3(px,(p217) => p217.inputs[p217.pos++] == 46 && e18(p217) && linktree(p217,"name",e13) && or3(p217,(p215) => e27(p215) && linktree(p215,"param",e28) && e29(p215) && tagtree(p215,"Method"),(p216) => tagtree(p216,"Get")),(p222) => or3(p222,(p218) => e27(p218) && linktree(p218,"param",e28) && e29(p218) && tagtree(p218,"Apply"),(p221) => or3(p221,(p219) => e47(p219) && linktree(p219,"param",e28) && e48(p219) && tagtree(p219,"Index"),(p220) => e83(p220) && linktree(p220,"type",e13) && tagtree(p220,"CastExpr"))));
}

function e40(px){
  return newtree(px,0,(p92) => e47(p92) && linktree(p92,"left",e15) && or1(p92,(p88) => p88.inputs[p88.pos++] == 116 && p88.inputs[p88.pos++] == 111 && !(bits32(bs5,p88.inputs[p88.pos])),(p89) => p89.inputs[p89.pos++] == 46 && p89.inputs[p89.pos++] == 46) && or3(p92,(p90) => p90.inputs[p90.pos++] == 60 && tagtree(p90,"RangeUntilExpr"),(p91) => tagtree(p91,"RangeExpr")) && linktree(p92,"right",e15) && e48(p92),EmptyTag,0);
}

function e71(px){
  return or1(px,e80,(p204) => bits32(bs10,p204.inputs[p204.pos++]));
}

function e55(px){
  return px.inputs[px.pos++] == 34 && newtree(px,0,(p145) => many1(p145,e71) && tagtree(p145,"String"),EmptyTag,0) && px.inputs[px.pos++] == 34 && e18(px);
}

function e56(px){
  return px.inputs[px.pos++] == 39 && newtree(px,0,(p146) => many1(p146,e72) && tagtree(p146,"Char"),EmptyTag,0) && px.inputs[px.pos++] == 39 && e18(px);
}

function e53(px){
  return newtree(px,0,(p142) => linktree(p142,"name",(p137) => or3(p137,e55,e56)) && or1(p142,(p138) => p138.inputs[p138.pos++] == 58,(p141) => or1(p141,(p139) => p139.inputs[p139.pos++] == 61,(p140) => p140.inputs[p140.pos++] == 61 && p140.inputs[p140.pos++] == 62)) && e18(p142) && linktree(p142,"value",e15),EmptyTag,0);
}

function e52(px){
  return px.inputs[px.pos++] == 125 && e18(px);
}

function e49(px){
  return px.inputs[px.pos++] == 123 && e18(px);
}

function e42(px){
  return newtree(px,0,(p99) => e49(p99) && linktree(p99,"",e53) && many3(p99,(p98) => e17(p98) && linktree(p98,"",e53)) && tagtree(p99,"Dict") && e52(p99),EmptyTag,0);
}

function e51(px){
  return newtree(px,0,(p136) => linktree(p136,"name",e13) && or1(p136,(p132) => p132.inputs[p132.pos++] == 58,(p135) => or1(p135,(p133) => p133.inputs[p133.pos++] == 61,(p134) => p134.inputs[p134.pos++] == 61 && p134.inputs[p134.pos++] == 62)) && e18(p136) && linktree(p136,"value",e15),EmptyTag,0);
}

function e50(px){
  return newtree(px,0,(p131) => p131.inputs[p131.pos++] == 35 && linktree(p131,"name",e13),EmptyTag,0);
}

function e41(px){
  return newtree(px,0,(p97) => e49(p97) && many3(p97,(p95) => linktree(p95,"",(p94) => e50(p94) && or1(p94,e17,(p93) => true))) && linktree(p97,"",e51) && many3(p97,(p96) => e17(p96) && linktree(p96,"",e51)) && tagtree(p97,"Data") && e52(p97),EmptyTag,0);
}

function e62(px){
  return newtree(px,0,(p166) => bits32(bs7,p166.inputs[p166.pos++]) && p166.inputs[p166.pos++] == 97 && p166.inputs[p166.pos++] == 108 && p166.inputs[p166.pos++] == 115 && p166.inputs[p166.pos++] == 101 && or1(p166,(p164) => bits32(bs5,p164.inputs[p164.pos]) && !(bits32(bs5,p164.inputs[p164.pos])),(p165) => true) && tagtree(p166,"False"),EmptyTag,0) && e18(px);
}

function e61(px){
  return newtree(px,0,(p163) => bits32(bs6,p163.inputs[p163.pos++]) && p163.inputs[p163.pos++] == 114 && p163.inputs[p163.pos++] == 117 && p163.inputs[p163.pos++] == 101 && or1(p163,(p161) => bits32(bs5,p161.inputs[p161.pos]) && !(bits32(bs5,p161.inputs[p161.pos])),(p162) => true) && tagtree(p163,"True"),EmptyTag,0) && e18(px);
}

function e64(px){
  return newtree(px,0,(p178) => p178.inputs[p178.pos++] == 226 && p178.inputs[p178.pos++] == 151 && p178.inputs[p178.pos++] == 143 && tagtree(p178,"Pictogram"),EmptyTag,0) && e18(px);
}

function e63(px){
  return newtree(px,0,(p177) => bits32(bs8,p177.inputs[p177.pos++]) && or1(p177,(p167) => p167.inputs[p167.pos++] == 117 && p167.inputs[p167.pos++] == 108 && p167.inputs[p167.pos++] == 108,(p174) => or1(p174,(p168) => p168.inputs[p168.pos++] == 111 && p168.inputs[p168.pos++] == 110 && p168.inputs[p168.pos++] == 101,(p173) => or1(p173,(p169) => p169.inputs[p169.pos++] == 105 && p169.inputs[p169.pos++] == 108,(p172) => or1(p172,(p170) => p170.inputs[p170.pos++] == 85 && p170.inputs[p170.pos++] == 76 && p170.inputs[p170.pos++] == 76,(p171) => p171.inputs[p171.pos++] == 111 && p171.inputs[p171.pos++] == 116 && p171.inputs[p171.pos++] == 104 && p171.inputs[p171.pos++] == 105 && p171.inputs[p171.pos++] == 110 && p171.inputs[p171.pos++] == 103)))) && or1(p177,(p175) => bits32(bs5,p175.inputs[p175.pos]) && !(bits32(bs5,p175.inputs[p175.pos])),(p176) => true) && tagtree(p177,"Null"),EmptyTag,0) && e18(px);
}

function e70(px){
  return or3(px,(p198) => p198.inputs[p198.pos++] == 36 && p198.inputs[p198.pos++] == 123 && e15(p198) && p198.inputs[p198.pos++] == 125,(p203) => newtree(p203,0,(p202) => many1(p202,(p201) => not1(p201,(p199) => p199.inputs[p199.pos++] == 39 && p199.inputs[p199.pos++] == 39 && p199.inputs[p199.pos++] == 39) && not1(p201,(p200) => p200.inputs[p200.pos++] == 36 && p200.inputs[p200.pos++] == 123) && p201.pos < p201.length && mnext1(p201)) && tagtree(p202,"String"),EmptyTag,0));
}

function e54(px){
  return px.inputs[px.pos++] == 39 && px.inputs[px.pos++] == 39 && px.inputs[px.pos++] == 39 && newtree(px,0,(p144) => many11(p144,(p143) => linktree(p143,"",e70)) && tagtree(p144,"Template"),EmptyTag,0) && px.inputs[px.pos++] == 39 && px.inputs[px.pos++] == 39 && px.inputs[px.pos++] == 39;
}

function e57(px){
  return px.inputs[px.pos++] == 60 && newtree(px,0,(p147) => many1(p147,e73) && tagtree(p147,"Image"),EmptyTag,0) && px.inputs[px.pos++] == 62 && e18(px);
}

function e75(px){
  return or1(px,(p210) => p210.inputs[p210.pos++] == 48 && !(bits32(bs14,p210.inputs[p210.pos])),(p212) => bits32(bs15,p212.inputs[p212.pos++]) && many1(p212,(p211) => manychar(p211,bs16) && bits32(bs13,p211.inputs[p211.pos++])));
}

function e59(px){
  return newtree(px,0,(p152) => e75(p152) && p152.inputs[p152.pos++] == 47 && e75(p152) && tagtree(p152,"Rational"),EmptyTag,0) && e18(px) && or3(px,(p154) => foldtree(p154,0,"",(p153) => linktree(p153,"",e13) && tagtree(p153,"Unit"),EmptyTag,0),(p155) => true);
}

function e82(px){
  return bits32(bs25,px.inputs[px.pos++]) && or1(px,(p253) => bits32(bs26,p253.inputs[p253.pos++]),(p254) => true) && bits32(bs13,px.inputs[px.pos++]) && many1(px,(p255) => manychar(p255,bs16) && bits32(bs13,p255.inputs[p255.pos++]));
}

function e81(px){
  return or1(px,(p250) => !(p250.inputs[p250.pos] == 95) && many1(p250,(p248) => manychar(p248,bs16) && bits32(bs13,p248.inputs[p248.pos++])) && p250.inputs[p250.pos++] == 46 && bits32(bs13,p250.inputs[p250.pos++]) && many1(p250,(p249) => manychar(p249,bs16) && bits32(bs13,p249.inputs[p249.pos++])),(p252) => bits32(bs13,p252.inputs[p252.pos++]) && many1(p252,(p251) => manychar(p251,bs16) && bits32(bs13,p251.inputs[p251.pos++])) && p252.inputs[p252.pos++] == 46 && !(p252.inputs[p252.pos] == 46));
}

function e74(px){
  return or1(px,(p208) => e81(p208) && or1(p208,e82,(p207) => true),(p209) => bits32(bs13,p209.inputs[p209.pos++]) && manychar(p209,bs13) && e82(p209));
}

function e58(px){
  return newtree(px,0,(p148) => e74(p148) && tagtree(p148,"Double"),EmptyTag,0) && e18(px) && or3(px,(p150) => foldtree(p150,0,"",(p149) => linktree(p149,"",e13) && tagtree(p149,"Unit"),EmptyTag,0),(p151) => true);
}

function e77(px){
  return px.inputs[px.pos++] == 48 && bits32(bs19,px.inputs[px.pos++]) && bits32(bs20,px.inputs[px.pos++]) && many1(px,(p214) => manychar(p214,bs16) && bits32(bs20,p214.inputs[p214.pos++]));
}

function e76(px){
  return px.inputs[px.pos++] == 48 && bits32(bs17,px.inputs[px.pos++]) && bits32(bs18,px.inputs[px.pos++]) && many1(px,(p213) => manychar(p213,bs16) && bits32(bs18,p213.inputs[p213.pos++]));
}

function e60(px){
  return newtree(px,0,(p157) => or1(p157,e75,(p156) => or1(p156,e76,e77)) && tagtree(p157,"Int"),EmptyTag,0) && e18(px) && or3(px,(p159) => foldtree(p159,0,"",(p158) => linktree(p158,"",e13) && tagtree(p158,"Unit"),EmptyTag,0),(p160) => true);
}

function e43(px){
  return or3(px,e54,(p108) => or3(p108,e55,(p107) => or3(p107,e56,(p106) => or3(p106,e57,(p105) => or3(p105,e58,(p104) => or3(p104,e59,(p103) => or3(p103,e60,(p102) => or3(p102,e61,(p101) => or3(p101,e62,(p100) => or3(p100,e63,e64))))))))));
}

function e37(px){
  return e27(px) && e15(px) && or3(px,(p81) => foldtree(p81,0,"",(p80) => e17(p80) && linktree(p80,"",e15) && many3(p80,(p79) => e17(p79) && linktree(p79,"",e15)) && tagtree(p80,"Tuple"),EmptyTag,0),(p82) => true) && e29(px);
}

function e39(px){
  return newtree(px,0,(p87) => e47(p87) && or3(p87,(p84) => linktree(p84,"",e15),(p85) => true) && many3(p87,(p86) => e17(p86) && many1(p86,e17) && linktree(p86,"",e15)) && many1(p87,e17) && e48(p87) && tagtree(p87,"List"),EmptyTag,0);
}

function e38(px){
  return newtree(px,0,(p83) => e27(p83) && e29(p83) && tagtree(p83,"Empty"),EmptyTag,0) && e18(px);
}

function e26(px){
  return or3(px,e37,(p67) => or3(p67,e38,(p66) => or3(p66,e39,(p65) => or3(p65,e40,(p64) => or3(p64,e41,(p63) => or3(p63,e42,(p62) => or3(p62,e43,e13)))))));
}

function e65(px){
  return e26(px) && many3(px,(p179) => foldtree(p179,0,"recv",e78,EmptyTag,0));
}

function e44(px){
  return or3(px,e65,(p113) => or3(p113,(p110) => newtree(p110,0,(p109) => linktree(p109,"op",e66) && linktree(p109,"expr",e67) && tagtree(p109,"Unary"),EmptyTag,0),(p112) => newtree(p112,0,(p111) => p111.inputs[p111.pos++] == 124 && e18(p111) && linktree(p111,"expr",e15) && p111.inputs[p111.pos++] == 124 && tagtree(p111,"Norm"),EmptyTag,0) && e18(p112)));
}

function e67(px){
  return or3(px,(p188) => newtree(p188,0,(p187) => e27(p187) && linktree(p187,"type",e13) && e29(p187) && linktree(p187,"recv",e67) && tagtree(p187,"Cast"),EmptyTag,0),e44);
}

function e68(px){
  return e67(px) && many3(px,(p190) => foldtree(p190,0,"left",(p189) => linktree(p189,"op",e79) && linktree(p189,"right",e67) && tagtree(p189,"Infix"),EmptyTag,0));
}

function e69(px){
  return newtree(px,0,(p197) => or1(p197,(p191) => p191.inputs[p191.pos++] == 43 && p191.inputs[p191.pos++] == 43,(p196) => or1(p196,(p192) => p192.inputs[p192.pos++] == 43,(p195) => or1(p195,(p193) => p193.inputs[p193.pos++] == 45,(p194) => p194.inputs[p194.pos++] == 124 && !(p194.inputs[p194.pos] == 124)))) && tagtree(p197,"Name"),EmptyTag,0) && e18(px);
}

function e45(px){
  return e68(px) && many3(px,(p115) => foldtree(p115,0,"left",(p114) => linktree(p114,"op",e69) && linktree(p114,"right",e68) && tagtree(p114,"Infix"),EmptyTag,0));
}

function e35(px){
  return e45(px) && many3(px,(p75) => foldtree(p75,0,"left",(p74) => linktree(p74,"op",e46) && linktree(p74,"right",e45) && tagtree(p74,"Infix"),EmptyTag,0));
}

function e36(px){
  return newtree(px,0,(p78) => or1(p78,(p76) => p76.inputs[p76.pos++] == 97 && p76.inputs[p76.pos++] == 110 && p76.inputs[p76.pos++] == 100 && !(bits32(bs5,p76.inputs[p76.pos])),(p77) => p77.inputs[p77.pos++] == 38 && p77.inputs[p77.pos++] == 38 && !(p77.inputs[p77.pos] == 38)) && tagtree(p78,"Name"),EmptyTag,0) && e18(px);
}

function e24(px){
  return e35(px) && many3(px,(p58) => foldtree(p58,0,"left",(p57) => linktree(p57,"op",e36) && linktree(p57,"right",e35) && tagtree(p57,"Infix"),EmptyTag,0));
}

function e25(px){
  return newtree(px,0,(p61) => or1(p61,(p59) => p59.inputs[p59.pos++] == 111 && p59.inputs[p59.pos++] == 114 && !(bits32(bs5,p59.inputs[p59.pos])),(p60) => p60.inputs[p60.pos++] == 124 && p60.inputs[p60.pos++] == 124 && !(p60.inputs[p60.pos] == 124)) && tagtree(p61,"Name"),EmptyTag,0) && px.inputs[px.pos++] == 95 && px.inputs[px.pos++] == 227 && px.inputs[px.pos++] == 128 && px.inputs[px.pos++] == 128;
}

function e15(px){
  return e24(px) && many3(px,(p43) => foldtree(p43,0,"left",(p42) => linktree(p42,"op",e25) && linktree(p42,"right",e24) && tagtree(p42,"Infix"),EmptyTag,0));
}

function e31(px){
  return newtree(px,0,(p72) => p72.inputs[p72.pos++] == 61 && p72.inputs[p72.pos++] == 62 && e18(p72) && linktree(p72,"expr",e15) && tagtree(p72,"Return"),EmptyTag,0);
}

function e14(px){
  return px.inputs[px.pos++] == 61 && e18(px);
}

function e32(px){
  return newtree(px,0,(p73) => p73.inputs[p73.pos++] == 36 && linktree(p73,"left",e44) && e14(p73) && linktree(p73,"right",e15) && tagtree(p73,"Assign"),EmptyTag,0);
}

function e19(px){
  return or3(px,(p49) => newtree(p49,0,(p48) => p48.inputs[p48.pos++] == 102 && p48.inputs[p48.pos++] == 111 && p48.inputs[p48.pos++] == 114 && p48.inputs[p48.pos++] == 101 && p48.inputs[p48.pos++] == 97 && p48.inputs[p48.pos++] == 99 && p48.inputs[p48.pos++] == 104 && e30(p48) && linktree(p48,"",e13) && p48.inputs[p48.pos++] == 115 && p48.inputs[p48.pos++] == 111 && p48.inputs[p48.pos++] == 109 && p48.inputs[p48.pos++] == 101 && linktree(p48,"",e13) && tagtree(p48,"PeriodicSome"),EmptyTag,0),(p55) => or3(p55,(p52) => newtree(p52,0,(p51) => p51.inputs[p51.pos++] == 102 && p51.inputs[p51.pos++] == 111 && p51.inputs[p51.pos++] == 114 && p51.inputs[p51.pos++] == 101 && p51.inputs[p51.pos++] == 97 && p51.inputs[p51.pos++] == 99 && p51.inputs[p51.pos++] == 104 && e30(p51) && linktree(p51,"",e13) && many3(p51,(p50) => e17(p50) && linktree(p50,"",e13)) && tagtree(p51,"Periodic"),EmptyTag,0),(p54) => newtree(p54,0,(p53) => p53.inputs[p53.pos++] == 119 && p53.inputs[p53.pos++] == 104 && p53.inputs[p53.pos++] == 101 && p53.inputs[p53.pos++] == 110 && e30(p53) && linktree(p53,"",e15) && tagtree(p53,"Event"),EmptyTag,0)));
}

function e11(px){
  return or3(px,(p30) => newtree(p30,0,(p29) => linktree(p29,"timing",e19) && many3(p29,(p28) => e18(p28) && or1(p28,e17,(p27) => true) && linktree(p28,"",e15)) && tagtree(p29,"TimingPremise"),EmptyTag,0),(p34) => newtree(p34,0,(p33) => linktree(p33,"",e15) && many3(p33,(p32) => e18(p32) && or1(p32,e17,(p31) => true) && linktree(p32,"",e15)) && tagtree(p33,"Premise"),EmptyTag,0));
}

function e10(px){
  return newtree(px,0,(p26) => linktree(p26,"",e13) && many3(p26,(p25) => e17(p25) && linktree(p25,"",e13)) && p26.inputs[p26.pos++] == 124 && p26.inputs[p26.pos++] == 62 && e18(p26) && tagtree(p26,"Context"),EmptyTag,0);
}

function e20(px){
  return bits32(bs3,px.inputs[px.pos++]) && manychar(px,bs3);
}

function e7(px){
  return newtree(px,0,(p20) => linktree(p20,"left",e13) && e14(p20) && linktree(p20,"right",e15) && tagtree(p20,"Let"),EmptyTag,0);
}

function e21(px){
  return or3(px,e31,(p56) => or3(p56,e32,e7));
}

function e12(px){
  return newtree(px,0,(p38) => linktree(p38,"",(p35) => e20(p35) && e21(p35) && e8(p35)) && many3(p38,(p37) => linktree(p37,"",(p36) => e20(p36) && e21(p36) && e8(p36))) && tagtree(p38,"Body"),EmptyTag,0);
}

function e16(px){
  return e26(px) && foldtree(px,0,"recv",(p44) => e27(p44) && linktree(p44,"param",e28) && e29(p44) && tagtree(p44,"Apply"),EmptyTag,0);
}

function e6(px){
  return newtree(px,0,(p19) => or3(p19,(p16) => linktree(p16,"context",e10),(p17) => true) && linktree(p19,"cond",e11) && e8(p19) && p19.inputs[p19.pos++] == 45 && p19.inputs[p19.pos++] == 45 && p19.inputs[p19.pos++] == 45 && manychar(p19,bs1) && many1(p19,(p18) => not1(p18,e8) && p18.pos < p18.length && mnext1(p18)) && e8(p19) && linktree(p19,"body",e12) && tagtree(p19,"Rule"),EmptyTag,0);
}

function e9(px){
  return newtree(px,0,(p24) => linktree(p24,"",e16) && tagtree(p24,"Position"),EmptyTag,0);
}

function e2(px){
  return or3(px,e6,(p8) => or3(p8,(p6) => e7(p6) && e8(p6),(p7) => e9(p7) && e8(p7)));
}

function e0(px){
  return e1(px) && newtree(px,0,(p2) => many3(p2,(p1) => linktree(p1,"",(p0) => e2(p0) && e1(p0))) && tagtree(p2,"Source"),EmptyTag,0) && e1(px) && e3(px);
}

function parse(inputs,length){
  var px = new ParserContext(inputs,length,memolen);
  if(e0(px)){
    if(px.tree == null){
      return new ctree(EmptyTag, inputs, 0, px.pos, null);
    }
    return px.tree;
  }
  return new ctree("[error]", inputs, 0, px.headpos, null);
}

// var fs = require('fs');

// (function main(){
//     for(var i = 2;i < process.argv.length;i++){
//       var inputs = fs.readFileSync('./' + process.argv[i]);
//       console.time('timer1');
//       var result = parse(inputs,inputs.length-1);
//       console.timeEnd('timer1');
//       console.log(result.toString());
//       //以下の関数を使うとObjectの中身まで見れますがxmark10.xmlみたいな大きなファイルの場合にコンソールが凍ります。
//       //console.dir(JSON.stringify(result));
//     }
// })();
    
