const images = {
    "<sakura>":"image/sakura.png",
    "<fish>":"image/fish.png",
    "<star>":"image/star.png",
    "<arrow>":"image/arrow.png",
    "<triangle>":"image/triangle.png",
    "<rocket>":"image/rocket.png"
};
const motype = {
    IMAGE: 1,
    NUMBER: 2,
    STRING: 3
};
const ttag = {
    Source: "Source",
    Rule: "Rule",
    Context: "Context",
    Premise: "Premise",
    PeriodicSome: "PeriodicSome",
    Periodic: "Periodic",
    Event: "Event",
    Body: "Body",
    Let: "Let",
    Assign: "Assign",
    Return: "Return",
    Name: "Name",
    Infix: "Infix",
    Cast: "Cast",
    Unary: "Unary",
    Norm: "Norm",
    Method: "Method",
    Get: "Get",
    Apply: "Apply",
    Index: "Index",
    CastExpr: "CastExpr",
    Tuple: "Tuple",
    Empty: "Empty",
    List: "List",
    RangeUntilExpr: "RangeUntilExpr",
    RangeExpr: "RangeExpr",
    Dict: "Dict",
    Data: "Data",
    Template: "Template",
    String: "String",
    Char: "Char",
    Image: "Image",
    Rational: "Rational",
    Unit: "Unit",
    Int: "Int",
    Double: "Double",
    True: "True",
    False: "False",
    Null: "Null"
};

const objh = 64;
const objw = 64;
var objPos = [0,0];

function nextPos (){
    if(objPos[0] + objw <= cvsw){
        objPos[0] = objPos[0] + objw;
    }else{
        objPos[0] = 0;
        objPos[1] = objPos[1] + objh;
    }
}

class MObject {
    constructor(value) {
        this.value = value;
    }
}
class MImage extends MObject {
    constructor(value) {
        super(value);
        this.img = new Image();
        this.img.src = "image/" + value + ".png";
        this.visible = true;
        this.type = motype.IMAGE;

        this.x = objPos[0];
        this.y = objPos[1];
        nextPos();
        this.h = objh;
        this.w = objw;
        this.a = 0;
        this.ix = this.x;
        this.iy = this.y;
        this.ih = this.h;
        this.iw = this.w;
        this.ia = this.a;
    }

    init(){
        this.x = this.ix;
        this.y = this.iy;
        this.h = this.ih;
        this.w = this.iw;
        this.a = this.ia;
    }
}
class MNumber extends MObject {
    constructor(value) {
        super(value);
        this.value = value;
        this.type = motype.NUMBER;
    }
}
class MString extends MObject {
    constructor(value) {
        super(value);
        this.value = value;
        this.type = motype.STRING;
    }
}
class MEmpty extends MObject {
    constructor(value){
        super(value);
    }
}
class Transition {
    constructor(){

    }
}

var globalField = {};
var currentField = globalField;
var Transitions = [];
var TransitionCount = 0;
var currentTransition = -1;
var svariableCount = 0;
var showFlipper = false;
function createImage(input) {
    return new MImage(input);
}
function createTransition(){
    var transition;
    transition = new Transition();
    Transitions.push(transition);
    TransitionCount++;
    return transition;
}
function evalTree(tree,info){
    switch(tree.tag){
        case ttag.Source:
            evalList(tree.child,info);
            return null;
        case ttag.Rule:
            if(info.inFlow){
                var before = currentField;
                currentField = {};
                evalLabeledTree(tree.child,"context",info); // TODO
                for(var obj in globalField){
                    info.currentObject = globalField[obj];
                    if(evalLabeledTree(tree.child,"cond",info)){
                        info.isKey = false;
                        evalLabeledTree(tree.child,"body",info);
                    }
                }
                currentField = before;
            }
            return null;
        case ttag.Context:
            return null; // TODO
        case ttag.Premise:
            var length = getLength(tree.child);
            var targets = evalElement(tree.child,0,info);
            if(Array.isArray(targets)){
                currentField[targets[0]] = info.currentObject;
            }else if(targets === false){
                return false;
            }
            for(var i = 1;i<length;i++){
                if(!evalElement(tree.child,i,info)){
                    return false;
                }
            }
            return true;
        case ttag.PeriodicSome: // TODO
            var targets = [];
            targets.push(evalElement(tree.child,0,{inFlow:true,isKey:true}));
            targets.push(evalElement(tree.child,1,{inFlow:true,isKey:true}));
            return targets;
        case ttag.Periodic:
            var length = getLength(tree.child);
            var targets = []
            for(var i = 0;i<length;i++){
                targets.push(evalElement(tree.child,i,{inFlow:true,isKey:true}));
            }
            return targets;
        case ttag.Event:
            return null; // TODO
        case ttag.Body:
            evalList(tree.child,info);
            return null;
        case ttag.Assign:
            var right = evalLabeledTree(tree.child,"right",info);
            info.isKey = true;
            var val = null;
            try{
                val = eval("currentField." + evalLabeledTree(tree.child,"left",info) + " = " + right);
            }catch(e){
                try{
                    val = eval("globalField." + evalLabeledTree(tree.child,"left",info) + " = " + right);
                }catch(e){
                    val = eval(evalLabeledTree(tree.child,"left",info) + " = " + right);
                }
            }
            info.isKey = false;
            return null;
        case ttag.Return:
            return null; // TODO
        case ttag.Let:
            if(!(info.inFlow)){
                currentField[evalLabeledTree(tree.child,"left",{inFlow:false,isKey:true})] = evalLabeledTree(tree.child,"right",{inFlow:false,createNew:true});
            }
            return null;
        case ttag.Infix:
            if(info.isKey){
                return evalLabeledTree(tree.child,"left",info) + evalLabeledTree(tree.child,"op",info) + evalLabeledTree(tree.child,"right",info);
            }
            var left = evalLabeledTree(tree.child,"left",info);
            var right = evalLabeledTree(tree.child,"right",info);
            if(MObject.prototype.isPrototypeOf(left)){
                left = left.value;
            }
            if(MObject.prototype.isPrototypeOf(right)){
                right = right.value;
            }
            var ret = left + evalLabeledTree(tree.child,"op",{isKey:true}) + right;
            return eval(ret);
        case ttag.Cast:
            if(info.isKey){
                return "(" + evalLabeledTree(tree.child,"type",info) + ")" + evalLabeledTree(tree.child,"recv",info);
            }
            return eval("(" + evalLabeledTree(tree.child,"type",info) + ")" + evalLabeledTree(tree.child,"recv",info));
        case ttag.Unary:
            if(info.isKey){
                return evalLabeledTree(tree.child,"op",info) + evalLabeledTree(tree.child,"expr",info);
            }
            return eval(evalLabeledTree(tree.child,"op",info) + evalLabeledTree(tree.child,"expr",info));
        case ttag.Norm:
            if(info.isKey){
                return "|" + evalLabeledTree(tree.child,"expr",info) + "|";
            }
            return eval("|" + evalLabeledTree(tree.child,"expr",info) + "|");
        case ttag.Method:
            if(info.isKey){
                return evalLabeledTree(tree.child,"recv",info) + "." + evalLabeledTree(tree.child,"name",info) + "(" + evalLabeledTree(tree.child,"param",info) + ")";
            }
            info.isKey = true;
            var val = null;
            try{
                val = eval("currentField." + evalLabeledTree(tree.child,"recv",info) + "." + evalLabeledTree(tree.child,"name",info) + "(" + evalLabeledTree(tree.child,"param",info) + ")");
            }catch(e){
                try{
                    val = eval("globalField." + evalLabeledTree(tree.child,"recv",info) + "." + evalLabeledTree(tree.child,"name",info) + "(" + evalLabeledTree(tree.child,"param",info) + ")");
                }catch(e){
                    val = eval(evalLabeledTree(tree.child,"recv",info) + "." + evalLabeledTree(tree.child,"name",info) + "(" + evalLabeledTree(tree.child,"param",info) + ")");
                }
            }
            info.isKey = false;
            return val;
        case ttag.Get:
            if(info.isKey){
                return evalLabeledTree(tree.child,"recv",info) + "." + evalLabeledTree(tree.child,"name",info);
            }
            info.isKey = true;
            var val = null;
            try{
                val = eval("currentField." + evalLabeledTree(tree.child,"recv",info) + "." + evalLabeledTree(tree.child,"name",info));
            }catch(e){
                try{
                    val = eval("globalField." + evalLabeledTree(tree.child,"recv",info) + "." + evalLabeledTree(tree.child,"name",info));
                }catch(e){
                    val = eval(evalLabeledTree(tree.child,"recv",info) + "." + evalLabeledTree(tree.child,"name",info));
                }
            }
            info.isKey = false;
            return val;
        case ttag.Apply:
            if(info.isKey){
                return evalLabeledTree(tree.child,"recv",info) + "(" + evalLabeledTree(tree.child,"param",info) + ")";
            }
            info.isKey = true;
            var val = null;
            try{
                val = eval("currentField." + evalLabeledTree(tree.child,"recv",info) + "(" + evalLabeledTree(tree.child,"param",info) + ")");
            }catch(e){
                try{
                    val = eval("globalField." + evalLabeledTree(tree.child,"recv",info) + "(" + evalLabeledTree(tree.child,"param",info) + ")");
                }catch(e){
                    val = eval(evalLabeledTree(tree.child,"recv",info) + "(" + evalLabeledTree(tree.child,"param",info) + ")");
                }
            }
            info.isKey = false;
            return val;
        case ttag.Index:
            if(info.isKey){
                return evalLabeledTree(tree.child,"recv",info) + "[" + evalLabeledTree(tree.child,"param",info) + "]";
            }
            info.isKey = true;
            var val = null;
            try{
                val = eval("currentField." + evalLabeledTree(tree.child,"recv",info) + "[" + evalLabeledTree(tree.child,"param",info) + "]");
            }catch(e){
                try{
                    val = eval("globalField." + evalLabeledTree(tree.child,"recv",info) + "[" + evalLabeledTree(tree.child,"param",info) + "]");
                }catch(e){
                    val = eval(evalLabeledTree(tree.child,"recv",info) + "[" + evalLabeledTree(tree.child,"param",info) + "]");
                }
            }
            info.isKey = false;
            return val;
        case ttag.CastExpr:
            if(info.isKey){
                return evalLabeledTree(tree.child,"recv",info) + "=>" + evalLabeledTree(tree.child,"type",info);
            }
            info.isKey = true;
            var val = null;
            try{
                val = eval("currentField." + evalLabeledTree(tree.child,"recv",info) + "=>" + evalLabeledTree(tree.child,"type",info));
            }catch(e){
                try{
                    val = eval("globalField." + evalLabeledTree(tree.child,"recv",info) + "=>" + evalLabeledTree(tree.child,"type",info));
                }catch(e){
                    val = eval(evalLabeledTree(tree.child,"recv",info) + "=>" + evalLabeledTree(tree.child,"type",info));
                }
            }
            info.isKey = false;
            return val;
        case ttag.Tuple:
            evalList(tree.child,info);
            return null; // TODO
        case ttag.Empty:
            return null;
        case ttag.List:
            evalList(tree.child,info);
            return null; // TODO
        case ttag.RangeUntilExpr:
            return null; // TODO
        case ttag.RangeExpr:
            return null; // TODO
        case ttag.Data:
            return null; // TODO
        case ttag.Dict:
            return null; // TODO
        case ttag.Tamplete:
            return null; // TODO
        case ttag.String:
            return "\"" + getValue(tree) + "\"";
        case ttag.Char:
            return "\'" + getValue(tree) + "\'";
        case ttag.Image:
            if(info.createNew){
                return createImage(getValue(tree));
            }
            return new MEmpty(getValue(tree));
        case ttag.Double:
            return getValue(tree);
        case ttag.Unit:
            return null; // TODO
        case ttag.Rational:
            return eval(getValue(tree));
        case ttag.Int:
            return getValue(tree);
        case ttag.True:
            return true;
        case ttag.False:
            return false;
        case ttag.Null:
            return null;
        case ttag.Name:
            var val = getValue(tree);
            if(info.isKey){
                return val;
            }
            if(val in currentField){
                return currentField[val];
            }
            if(val in globalField){
                return globalField[val];
            }
            return val;
        default:
    }
}

// :string
function getValue(tree){
    var inputs = tree.inputs.slice(tree.spos,tree.epos);
    return (new TextDecoder).decode(inputs);
}

function evalLabeledTree(tree,label,info){
    if(tree.tag === label){
        return evalTree(tree.child,info);
    }else if(tree.prev !== null){
        return evalLabeledTree(tree.prev,label,info);
    }
    return null;
}

function evalElement(tree,index,info){
    var i = getLength(tree) - index;
    var target = tree;
    while(i>0){
        target = target.prev;
        i--;
    }
    return evalTree(target.child,info);
}

function getLength(tree){
    var length = 0;
    var target = tree;
    while(target.prev !== null){
        target = target.prev;
        length++;
    }
    return length;
}

function evalList(tree,info){
    if(tree.prev !== null){
        evalList(tree.prev,info);
    }
    if(tree.child !== null){
        evalTree(tree.child,info);
    }
}

function showTree(tree,depth){
    var indent = showFlipper ? "=".repeat(depth) : "-".repeat(depth);
    showFlipper = !showFlipper;
    console.log(indent + tree.tag);
    if(tree.child.prev !== null){
        if(tree.child.prev.prev !== null){
            showChild(tree.child.prev.prev,depth);
        }
        showTree(tree.child.prev.child,depth+1);
    }
}

function showChild(tree,depth){
    if(tree.prev !== null){
        showChild(tree.prev,depth);
    }
    showTree(tree.child,depth+1);
}

var canvas = document.getElementById("cvs");
var ctx = canvas.getContext("2d");
var cvsw = 900;
var cvsh = 900;
var cos = 0;
var sin = 0;
var rad = Math.PI / 180;
var timeCounter = 0;
var timer;
var result;
var Mouse = {
    x:0,
    y:0
};
canvas.addEventListener('mousemove', function (evt) {
    var mousePos = getMousePosition(canvas, evt);
    Mouse.x = mousePos.x;
    Mouse.y = mousePos.y;
}, false);
function getMousePosition(canvas, evt) {
    var rect = canvas.getBoundingClientRect();
    return {
        x: evt.clientX - rect.left,
        y: evt.clientY - rect.top
    };
}
function plot() {
    ctx.clearRect(0, 0, cvsw, cvsh);
    for(var obj in globalField) {
        if(MImage.prototype.isPrototypeOf(globalField[obj])){
            cos = Math.cos(globalField[obj].a * rad);
            sin = Math.sin(globalField[obj].a * rad);
            ctx.setTransform(cos, sin, -1 * sin, cos, globalField[obj].x, globalField[obj].y);
            ctx.drawImage(globalField[obj].img, 0, 0, globalField[obj].w, globalField[obj].h);
            ctx.setTransform(1, 0, 0, 1, 0, 0);
        }
    }
}
const initFuncs = ["POS", "RAND", "CENTER"];
function flow() {
    if(result !== null){
        evalTree(result,{inFlow:true});
    }
    for(var obj in globalField) {
        if(MImage.prototype.isPrototypeOf(globalField[obj])){
            if(globalField[obj].x > cvsw) globalField[obj].x -= cvsw;
            if(globalField[obj].x < 0) globalField[obj].x += cvsw;
            if(globalField[obj].y > cvsh) globalField[obj].y -= cvsh;
            if(globalField[obj].y < 0) globalField[obj].y += cvsh;
            if(globalField[obj].a > 360) globalField[obj].a -= 360;
            if(globalField[obj].a < 0) globalField[obj].a += 360;
        }
    }
    plot();
    $(function(){
        $("#time-counter").text(++timeCounter);
    });
}
function flowStart() {
    timer = setInterval(flow, 20);
}
function flowPause() {
    clearInterval(timer);
}
function incrementFrame() {
    flow();
}
function init() {
    for(var obj in globalField){
        if(MImage.prototype.isPrototypeOf(globalField[obj])){
            globalField[obj].init();
        }
    }
    plot();
    timeCounter = 0;
    $(function(){
        $("#time-counter").text(timeCounter);
    });
}

$(function () {
    var initCode = "s = <sakura>\nforeach a  a == <sakura>\n-------------------\n    $a.x = a.x + 10";
    $('#source-text').val(initCode);
    var jsEditor = makeEditor();
    cvsw = $('#mapping-area').width();
    cvsh = $('#mapping-area').height();
    $('#cvs').attr('width', cvsw);
    $('#cvs').attr('height', cvsh);
    var timer = false;
    $(window).resize(function() {
        if (timer !== false) {
            clearTimeout(timer);
        }
        timer = setTimeout(function() {
            console.log('resized');
            cvsw = $('#mapping-area').width();
            cvsh = $('#mapping-area').height();
            $('#cvs').attr('width', cvsw);
            $('#cvs').attr('height', cvsh);
        }, 200);
    });
    $('#parse').click(function () {
        console.log("parse");
        jsEditor.toTextArea();
        var inputs = (new TextEncoder).encode($('#source-text').val().toString());
        result = parse(inputs,inputs.length-1);
        jsEditor = makeEditor();
    });
    $('#eval').click(function () {
        console.log("eval");
        objPos = [0,0];
        globalField = {};
        currentField = globalField;
        evalTree(result,{inFlow:false});
        init();
    });
    $('#show').click(function() {
        showTree(result,0);
    });
    $('#start-plot').click(function () {
        console.log("start");
        $(this).removeClass("active");
        $($(this).attr("switch-link")).addClass("active");
        flowStart();
    });
    $('#pause-plot').click(function (){
        console.log("pause");
        $(this).removeClass("active");
        $($(this).attr("switch-link")).addClass("active");
        flowPause();
    });
    $('#increment-frame').click(function () {
        console.log("increment-frame");
        incrementFrame();
    });
    $('#reset').click(function () {
        console.log("reset");
        init();
    });
    $('#sakura').click(function (){
        console.log("sakura");
        jsEditor.toTextArea();
        var input = $('#source-text').val().toString();
        input = "_" + svariableCount + " = <sakura>\n" + input;
        svariableCount++;
        $('#source-text').val(input);
        jsEditor = makeEditor();
    });
    $('#fish').click(function (){
        console.log("fish");
        jsEditor.toTextArea();
        var input = $('#source-text').val().toString();
        input = "_" + svariableCount + " = <fish>\n" + input;
        svariableCount++;
        $('#source-text').val(input);
        jsEditor = makeEditor();
    });
    $('#star').click(function (){
        console.log("star");
        jsEditor.toTextArea();
        var input = $('#source-text').val().toString();
        input = "_" + svariableCount + " = <star>\n" + input;
        svariableCount++;
        $('#source-text').val(input);
        jsEditor = makeEditor();
    });
    $('#arrow').click(function (){
        console.log("arrow");
        jsEditor.toTextArea();
        var input = $('#source-text').val().toString();
        input = "_" + svariableCount + " = <arrow>\n" + input;
        svariableCount++;
        $('#source-text').val(input);
        jsEditor = makeEditor();
    });
    $('#rocket').click(function (){
        console.log("rocket");
        jsEditor.toTextArea();
        var input = $('#source-text').val().toString();
        input = "_" + svariableCount + " = <rocket>\n" + input;
        svariableCount++;
        $('#source-text').val(input);
        jsEditor = makeEditor();
    });
});

function makeEditor(){
    return CodeMirror.fromTextArea(document.getElementById("source-text"), {
        mode: "javascript",
        lineNumbers: false,
        indentUnit: 4
    });
}

function POS(posx,posy,obj){
    obj.x = posx;
    obj.y = posy;
    obj.ix = obj.x;
    obj.iy = obj.y;
}

function RAND(){
    for(obj of arguments){
        POS(Math.random()*cvsw, Math.random()*cvsh, obj);
    }
}

function CENTER(){
    var ys = [];
    for(obj of arguments){
        if(ys.indexOf(obj.y) < 0){
            ys.push(obj.y);
        }
    }
    for(posy of ys){
        var sumw = 0;
        for(obj of arguments){
            if(posy == obj.y){
                sumw = sumw + obj.w;
            }
            
        }
        var posx = (cvsw - sumw) / 2;
        for(obj of arguments){
            if(posy == obj.y){
                POS(posx, posy, obj);
                posx = posx + obj.w;
            }
        }
    }
}
