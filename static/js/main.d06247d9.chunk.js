/*! For license information please see main.d06247d9.chunk.js.LICENSE.txt */
(this["webpackJsonpreact-scroll-snap-tabs-example"]=this["webpackJsonpreact-scroll-snap-tabs-example"]||[]).push([[0],[,,function(e,t,n){},,,function(e,t,n){e.exports=n(11)},,,,,function(e,t,n){},function(e,t,n){"use strict";n.r(t);n(2);var r=n(0),o=n.n(r),i=n(4),a=n.n(i);function c(){return(c=Object.assign?Object.assign.bind():function(e){for(var t=1;t<arguments.length;t++){var n=arguments[t];for(var r in n)Object.prototype.hasOwnProperty.call(n,r)&&(e[r]=n[r])}return e}).apply(this,arguments)}function s(e,t){if(null==e)return{};var n,r,o={},i=Object.keys(e);for(r=0;r<i.length;r++)n=i[r],t.indexOf(n)>=0||(o[n]=e[n]);return o}function l(e,t){return e(t={exports:{}},t.exports),t.exports}var u="function"===typeof Symbol&&Symbol.for,f=u?Symbol.for("react.element"):60103,p=u?Symbol.for("react.portal"):60106,d=u?Symbol.for("react.fragment"):60107,v=u?Symbol.for("react.strict_mode"):60108,h=u?Symbol.for("react.profiler"):60114,y=u?Symbol.for("react.provider"):60109,b=u?Symbol.for("react.context"):60110,m=u?Symbol.for("react.async_mode"):60111,g=u?Symbol.for("react.concurrent_mode"):60111,w=u?Symbol.for("react.forward_ref"):60112,O=u?Symbol.for("react.suspense"):60113,C=u?Symbol.for("react.suspense_list"):60120,S=u?Symbol.for("react.memo"):60115,j=u?Symbol.for("react.lazy"):60116,k=u?Symbol.for("react.block"):60121,E=u?Symbol.for("react.fundamental"):60117,x=u?Symbol.for("react.responder"):60118,T=u?Symbol.for("react.scope"):60119;function L(e){if("object"===typeof e&&null!==e){var t=e.$$typeof;switch(t){case f:switch(e=e.type){case m:case g:case d:case h:case v:case O:return e;default:switch(e=e&&e.$$typeof){case b:case w:case j:case S:case y:return e;default:return t}}case p:return t}}}function _(e){return L(e)===g}var P={AsyncMode:m,ConcurrentMode:g,ContextConsumer:b,ContextProvider:y,Element:f,ForwardRef:w,Fragment:d,Lazy:j,Memo:S,Portal:p,Profiler:h,StrictMode:v,Suspense:O,isAsyncMode:function(e){return _(e)||L(e)===m},isConcurrentMode:_,isContextConsumer:function(e){return L(e)===b},isContextProvider:function(e){return L(e)===y},isElement:function(e){return"object"===typeof e&&null!==e&&e.$$typeof===f},isForwardRef:function(e){return L(e)===w},isFragment:function(e){return L(e)===d},isLazy:function(e){return L(e)===j},isMemo:function(e){return L(e)===S},isPortal:function(e){return L(e)===p},isProfiler:function(e){return L(e)===h},isStrictMode:function(e){return L(e)===v},isSuspense:function(e){return L(e)===O},isValidElementType:function(e){return"string"===typeof e||"function"===typeof e||e===d||e===g||e===h||e===v||e===O||e===C||"object"===typeof e&&null!==e&&(e.$$typeof===j||e.$$typeof===S||e.$$typeof===y||e.$$typeof===b||e.$$typeof===w||e.$$typeof===E||e.$$typeof===x||e.$$typeof===T||e.$$typeof===k)},typeOf:L},M=(l((function(e,t){0})),l((function(e){e.exports=P})),Object.getOwnPropertySymbols),I=Object.prototype.hasOwnProperty,R=Object.prototype.propertyIsEnumerable;function N(e){if(null===e||void 0===e)throw new TypeError("Object.assign cannot be called with null or undefined");return Object(e)}(function(){try{if(!Object.assign)return!1;var e=new String("abc");if(e[5]="de","5"===Object.getOwnPropertyNames(e)[0])return!1;for(var t={},n=0;n<10;n++)t["_"+String.fromCharCode(n)]=n;if("0123456789"!==Object.getOwnPropertyNames(t).map((function(e){return t[e]})).join(""))return!1;var r={};return"abcdefghijklmnopqrst".split("").forEach((function(e){r[e]=e})),"abcdefghijklmnopqrst"===Object.keys(Object.assign({},r)).join("")}catch(o){return!1}})()&&Object.assign;var V="SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED";Function.call.bind(Object.prototype.hasOwnProperty);function K(e,t,n,r,o){}K.resetWarningCache=function(){0};function D(){}function $(){}$.resetWarningCache=D;var W=l((function(e){e.exports=function(){function e(e,t,n,r,o,i){if(i!==V){var a=new Error("Calling PropTypes validators directly is not supported by the `prop-types` package. Use PropTypes.checkPropTypes() to call them. Read more at http://fb.me/use-check-prop-types");throw a.name="Invariant Violation",a}}function t(){return e}e.isRequired=e;var n={array:e,bigint:e,bool:e,func:e,number:e,object:e,string:e,symbol:e,any:e,arrayOf:t,element:e,elementType:e,instanceOf:t,node:e,objectOf:t,oneOf:t,oneOfType:t,shape:t,exact:t,checkPropTypes:$,resetWarningCache:D};return n.PropTypes=n,n}()})),z={"tab-content":"_XaRX6","tab-nav":"_3vo4o"},H={duration:300,easing:"ease-out",fireAnimationEndEventOnStop:!1},A=function(){function e(e){var t=c({},H,e);switch(t.easing){case"ease-in":t.timing=function(e){return e*e};break;case"ease-out":t.timing=function(e){return 1-Math.pow(1-e,2)};break;case"ease-in-out":t.timing=function(e){return e<.5?2*e*e:1-Math.pow(2-2*e,2)/2};break;default:if("function"===typeof t.easing){t.timing=t.easing;break}t.timing=function(e){return e}}this.options=t,this.stopped=!0,this.started=!1,this._events={}}var t=e.prototype;return t.start=function(){var e=this.options.timing,t=this.options.update,n=this.options.duration;if(!window.requestAnimationFrame)return t(1),this._events.end&&this._emit("end",this.progress),void console.warn("Your browser does not support window.requestAnimationFrame");var r=window.performance.now();this.requestId=window.requestAnimationFrame(function o(i){if(this.started||(this._events.start&&this._emit("start"),this.started=!0),this.stopped)this._events.end&&this.options.fireAnimationEndEventOnStop&&this.emit("end",this.progress);else{var a=(i-r)/n;a<0&&(a=0,r=i),a>1&&(a=1,this.stopped=!0,this._events.end&&this._emit("end",this.progress));var c=e(a);if(this.progress=c,this.options.fromTo){var s=this.options.fromTo,l=s[1]-s[0];t(s[0]+c*l)}else t(c);a<1&&(this.requestId=window.requestAnimationFrame(o.bind(this)))}}.bind(this))},t.stop=function(){window.cancelAnimationFrame(this.requestId),this.stopped=!0},t.update=function(e){return this.options.update=e,this.stopped=!1,this.started=!1,this},t.on=function(e,t){this._events[e]||(this._events[e]=[]),this._events[e].push(t)},t.removeListener=function(e,t){if(this._events[e]){this._events[e]=this._events[e].filter((function(e){return e!==t}))}},t.removeAllListeners=function(){this._events={}},t._emit=function(e,t){this._events[e]?this._events[e].forEach((function(e){e(t)})):console.warn("Can't emit an event. Event \""+e+"\" doesn't exits.")},e}(),Y=0;function q(e,t,n,o){var i=Object(r.useRef)();Object(r.useEffect)((function(){i.current=t}),[t]),Object(r.useEffect)((function(){if(n&&n.addEventListener){var t=function(e){return i.current(e)};return n.addEventListener(e,t,o),function(){return n.removeEventListener(e,t,o)}}}),[e,n])}var F=["children","defaultKey","eventKeys","style","className","layout","snapDuration","snapThreshold","swipeThreshold","easing","indicatorClass","indicatorColor","indicatorStyle","indicatorSize","onIndicatorMove","activeLinkClass","activeLinkStyle","indicatorParentStyle","indicatorParentClass","scrollIntoViewDuration","scrollIntoViewEasing","scrollIntoViewOffset","linkStyle","linkClass"],B=["eventKeys","className","activeLinkClass","activeLinkStyle","indicatorColor","indicatorClass","indicatorSize","indicatorStyle","onIndicatorMove","indicatorParentStyle","indicatorParentClass","scrollIntoViewDuration","scrollIntoViewEasing","scrollIntoViewOffset","children","style","linkStyle","linkClass","__TYPE"],X=["eventKey","className","children","style","activeStyle","activeClass","__TYPE"],J=["children","style","paneStyle","paneClass","className"],U=["children","eventKey","__TYPE"],G=o.a.createContext(),Q={vertical:{left:"left",width:"width",offsetLeft:"offsetLeft",offsetWidth:"offsetWidth",minHeight:"minHeight"},horizontal:{left:"top",width:"height",offsetLeft:"offsetTop",offsetWidth:"offsetHeight",minHeight:"minWidth"}},Z={vertical:{wrapperflexDirection:"column",flexDirection:"row",indicatorBottom:"0"},horizontal:{wrapperflexDirection:"row",flexDirection:"column",indicatorRight:"0"}};function ee(e){var t=e.children,n=e.defaultKey,i=e.eventKeys,a=e.style,l=e.className,u=e.layout,f=e.snapDuration,p=e.snapThreshold,d=e.swipeThreshold,v=e.easing,h=e.indicatorClass,y=e.indicatorColor,b=e.indicatorStyle,m=e.indicatorSize,g=e.onIndicatorMove,w=e.activeLinkClass,O=e.activeLinkStyle,C=e.indicatorParentStyle,S=e.indicatorParentClass,j=e.scrollIntoViewDuration,k=e.scrollIntoViewEasing,E=e.scrollIntoViewOffset,x=e.linkStyle,T=e.linkClass,L=s(e,F),_="horizontal"===u?Z.horizontal:Z.vertical,P="horizontal"===u?Q.horizontal:Q.vertical,M=Object(r.useState)(null),I=M[0],R=M[1],N=Object(r.useState)([]),V=N[0],K=N[1],D=Object(r.useRef)(null),$=Object(r.useRef)(g),W=Object(r.useRef)(null),H=Object(r.useRef)(null),A=Object(r.useRef)(new Map);return Object(r.useEffect)((function(){!I&&V.length>0&&R(n||V[0])}),[V,R]),o.a.createElement(G.Provider,{value:{eventHandler:[I,R],events:[V,K],indicatorRef:D,contentRef:W,linkMapRef:A,onIndicatorMoveRef:$,snapTo:H,propValues:_,propNames:P,defaultKey:n||V[0],navOptions:{indicatorClass:h,indicatorStyle:b,indicatorColor:y,activeLinkClass:w,activeLinkStyle:O,indicatorParentStyle:C,indicatorParentClass:S,indicatorSize:m,scrollIntoViewDuration:j,scrollIntoViewEasing:k,scrollIntoViewOffset:E,linkStyle:x,linkClass:T},options:{duration:f,easing:v,threshold:p,swipeThreshold:d}}},o.a.createElement("div",c({className:[z.tabs,l].join(" ").trim(),style:c({display:"flex",flexDirection:_.wrapperflexDirection,height:"100%",width:"100%"},a)},L),i&&o.a.createElement(te,{eventKeys:i}),t))}function te(e){var t,n=e.eventKeys,i=e.className,a=e.activeLinkClass,l=e.activeLinkStyle,u=e.indicatorColor,f=e.indicatorClass,p=e.indicatorSize,d=e.indicatorStyle,v=e.onIndicatorMove,h=e.indicatorParentStyle,y=e.indicatorParentClass,b=e.scrollIntoViewDuration,m=e.scrollIntoViewEasing,g=e.scrollIntoViewOffset,w=e.children,O=e.style,C=e.linkStyle,S=e.linkClass,j=s(e,B),k=Object(r.useContext)(G),E=k.indicatorRef,x=k.propValues,T=k.propNames,L=k.navOptions,_=k.linkMapRef,P=k.eventHandler,M=k.onIndicatorMoveRef,I=k.layout,R=Object(r.useRef)(),N=P[0],V=function(e,t,n){void 0===t&&(t=250),void 0===n&&(n="ease-out");var o=Object(r.useRef)(new A({duration:t,easing:n})),i=Object(r.useCallback)((function(){var t=e.current;return{top:t.scrollTop,left:t.scrollLeft}}),[e]),a=Object(r.useCallback)((function(){var t=e.current,n=i();return c({},n,{bottom:n.top+t.clientHeight,right:n.left+t.clientWidth,scrollWidth:t.scrollWidth-t.clientWidth,scrollHeight:t.scrollHeight-t.clientHeight})}),[i,e]),s=Object(r.useCallback)((function(e){return{left:e.offsetLeft,top:e.offsetTop,right:e.offsetLeft+e.offsetWidth,bottom:e.offsetTop+e.offsetHeight}}),[]),l=Object(r.useCallback)((function(t){var n=e.current;if(window.document.contains)return n.contains(t);for(var r=t.parentNode;null!=r;){if(r===n)return!0;r=r.parentNode}return!1}),[e]),u=Object(r.useCallback)((function(t){var n=e.current,r=i(),a=t.left-r.left,c=t.top-r.top;o.current.stop(),o.current.update((function(e){n.scrollLeft=r.left+a*e,n.scrollTop=r.top+c*e})),o.current.start()}),[i,e]);return Object(r.useCallback)((function(e,t){if(l(e)){var n={};n.x="object"===typeof t?Number(t.x)||0:Number(t)||0,n.y="object"===typeof t?Number(t.y)||0:Number(t)||0;var r=a(),o=s(e),i=o.left-n.x>r.left&&o.right+n.x>r.right?o.right-r.right+n.x:o.left-n.x<r.left&&o.right+n.x<r.right?o.left-r.left-n.x:0,c=o.top>r.top&&o.bottom>r.bottom?o.bottom-r.bottom+n.y:o.top<r.top&&o.bottom<r.bottom?o.top-r.top-n.y:0,f=Math.max(0,Math.min(r.top+c,r.scrollHeight)),p=Math.max(0,Math.min(r.left+i,r.scrollWidth));u({top:f,left:p})}}),[l,a,s,u])}(R,b||L.scrollIntoViewDuration,m||L.scrollIntoViewEasing);Object(r.useLayoutEffect)((function(){"function"===typeof v&&(M.current=v)}),[]),Object(r.useEffect)((function(){V(_.current.get(N),g||L.scrollIntoViewOffset||100)}),[N,V,g]);var K=Object(r.useMemo)((function(){return w&&o.a.Children.map(w,(function(e){return o.a.isValidElement(e)&&"Link"===e.props.__TYPE?o.a.cloneElement(e,{style:c({},C,L.linkStyle,e.props.style),className:[e.props.className,S,L.linkClass].join(" ").trim(),activeClass:e.props.activeClass||a||L.activeLinkClass,activeStyle:c({},L.activeLinkStyle,l,e.props.activeStyle)}):e}))}),[w,a]),D={display:"flex",flexDirection:x.flexDirection,position:"relative",overflow:"auto",scrollbarWidth:"none"};return o.a.createElement("div",c({ref:R,style:c({},O,D),className:[z["tab-nav"],i].join(" ").trim()},j),K||n&&n.map((function(e,t){return o.a.createElement(ne,{key:t,eventKey:e,style:c({},L.linkStyle,C),className:S||L.linkClass,activeStyle:c({color:"#5A90E4"},L.activeLinkStyle,l),activeClass:a||L.activeLinkClass})})),o.a.createElement("div",{style:c({position:"absolute",bottom:x.indicatorBottom,right:x.indicatorRight},L.indicatorParentStyle,h),className:y||L.indicatorParentClass,ref:E},o.a.createElement("div",{className:f||L.indicatorClass||"",style:c((t={width:"horizontal"===I?"100%":p||L.indicatorSize,height:"horizontal"===I?p||L.indicatorSize:"100%",margin:"auto "},t[T.minHeight]="3px",t.backgroundColor=u||L.indicatorColor||"black",t),L.indicatorStyle,d)})))}function ne(e){var t=e.eventKey,n=e.className,i=e.children,a=e.style,l=e.activeStyle,u=e.activeClass,f=s(e,X),p=Object(r.useContext)(G),d=p.eventHandler,v=p.events,h=p.linkMapRef,y=d[0],b=d[1],m=v[1],g=Object(r.useRef)(null);Object(r.useLayoutEffect)((function(){m((function(e){return[].concat(e,[t])})),h.current.set(t,g.current)}),[t,m]);var w=y===t?[n,u].join(" ").trim():n,O=c({cursor:"pointer",padding:"0.5rem"},a);return o.a.createElement("div",c({onClick:function(e){b(t)},className:w,style:y===t?c({},O,l):O,ref:g},f),i||t)}function re(e){var t=e.children,n=e.style,i=e.paneStyle,a=e.paneClass,l=e.className,u=s(e,J),f=Object(r.useContext)(G),p=f.eventHandler,d=f.indicatorRef,v=f.options,h=f.events,y=f.linkMapRef,b=f.contentRef,m=f.snapTo,g=f.propValues,w=f.propNames,O=f.defaultKey,C=f.onIndicatorMoveRef,S=h[0],j=p[0],k=p[1],E=Object(r.useRef)(null),x=Object(r.useRef)(h.indexOf(j)),T=function(e){var t=e.scrollContainerRef,n=e.childrenSelector,o=void 0===n?"> div":n,i=e.threshold,a=void 0===i?30:i,s=e.swipeThreshold,l=void 0===s?200:s,u=e.easing,f=void 0===u?"ease-out":u,p=e.duration,d=void 0===p?250:p,v=e.onSnapStart,h=e.onSnap,y=Object(r.useState)(null),b=y[0],m=y[1],g=Object(r.useRef)(!1),w=Object(r.useRef)(null),O=Object(r.useRef)([]),C=Object(r.useRef)(),S=Object(r.useRef)(null),j=Object(r.useRef)(null),k=Object(r.useRef)(null),E=Object(r.useRef)(null);Object(r.useLayoutEffect)((function(){S.current=Y,t.current.dataset.snapContainerId=S.current,t.current.style.position="relative",w.current=new A({easing:f,duration:d}),Y++}),[]),Object(r.useLayoutEffect)((function(){var e='[data-snap-container-id="'+S.current+'"] '+o;O.current=Array.from(t.current.querySelectorAll(e)).reduce((function(e,t,n){return[].concat(e,[{index:n,top:t.offsetTop,left:t.offsetLeft,right:t.offsetLeft+t.offsetWidth,bottom:t.offsetTop+t.offsetHeight}])}),[]),C.current=O.current[0]}),[o,b]);var x=Object(r.useCallback)((function(){var e=t.current;return{top:e.scrollTop,left:e.scrollLeft}}),[]),T=Object(r.useCallback)((function(e,n){var r;if(e){n=n||x();var o=e.left-n.left,i=e.top-n.top;if(0===o&&0===i&&e.left===C.current.left&&e.top===C.current.top)return v&&v(e.index),void(C.current=e);null===(r=w.current)||void 0===r||r.stop(),w.current.update((function(e){var r=n.left+e*o,a=n.top+e*i;t.current.scrollTo({top:a,left:r})})),w.current.removeAllListeners(),w.current.on("start",(function(){v&&v(e.index),C.current=e})),w.current.on("end",(function(){clearTimeout(E.current),h&&h(e.index)})),w.current.start()}}),[x,v,h]),L=Object(r.useCallback)((function(e){var t=x(),n=c({},t,{right:t.left+e.clientWidth,bottom:t.top+e.clientHeight});return O.current.filter((function(e){return e.top<n.bottom&&e.bottom>n.top&&e.left<n.right&&e.right>n.left}))}),[x,O]),_=Object(r.useCallback)((function(e,n){var r=L(t.current),o=e<0||n<0?r[0].index+1:r[r.length-1].index-1;return O.current[o]||r[0]}),[L]),P=Object(r.useCallback)((function(){var e=L(t.current),n=x();return 1===e.length?e[0]:e.sort((function(e,t){var r=(e.left+t.left)/2,o=(e.top+t.top)/2,i=e.left>t.left||e.top>t.top?1:-1;return(r-n.left)*i||(o-n.top)*i}))[0]}),[L,x]),M=Object(r.useCallback)((function(e,t){if(Math.abs(e)<=5&&Math.abs(t)<=5)return!1;return Math.abs(t)>l||Math.abs(e)>l||function(){var e=625*Math.pow(10,-6),t=j.current.xSpeed>j.current.ySpeed?j.current.xSpeed:j.current.ySpeed;return t*t/(2*e)>l}()}),[l]),I=Object(r.useCallback)((function(){var e,t;if(w.current.stopped){var n,r=x(),o=((null===(e=k.current)||void 0===e?void 0:e.left)||C.current.left)-r.left,i=((null===(t=k.current)||void 0===t?void 0:t.top)||C.current.top)-r.top;if(j.current?M(o,i):Math.abs(o)>a||Math.abs(i)>a)n=_(o,i);else n=P();T(n,r)}}),[x,M,a,_,T]),R=Object(r.useCallback)((function(){t.current.style.overflow="auto"}),[]),N=Object(r.useCallback)((function(e){return function(t){clearTimeout(E.current),!g.current&&w.current.stopped&&(E.current=setTimeout((function(){R(),I()}),e))}}),[R,I]),V=Object(r.useCallback)((function(e){R(),N(66)()}),[R,N]),K=Object(r.useCallback)((function(){var e;k.current=x(),null===(e=w.current)||void 0===e||e.stop(),R(),g.current=!0}),[R]),D=Object(r.useCallback)((function(){g.current=!1,I(),k.current=null}),[I]),$=Object(r.useCallback)((function(e){var t=e.changedTouches[0];j.current={},j.current.xStart=t.clientX,j.current.yStart=t.clientY,j.current.startTime=window.performance?window.performance.now():Date.now(),K()}),[K]),W=Object(r.useCallback)((function(e){if(j.current){var n=e.changedTouches[0],r=(window.performance?window.performance.now():Date.now())-j.current.startTime;j.current.xSpeed=Math.abs(j.current.xStart-n.clientX)/r,j.current.ySpeed=Math.abs(j.current.yStart-n.clientY)/r,t.current.style.overflow="hidden",D(),j.current=null}}),[D]),z=Object(r.useMemo)((function(){var e=!1;try{var t={get passive(){return e=!0,!1}};window.addEventListener("test",null,t),window.removeEventListener("test",null,t)}catch(n){console.warn("window.addEventListener() does not support passive option")}return e}));return q("scroll",N(44),t.current,z&&{passive:!0}),q("touchstart",$,t.current,z&&{passive:!0}),q("touchend",W,t.current,z&&{passive:!0}),q("keydown",K,t.current,z&&{passive:!0}),q("keyup",D,t.current,z&&{passive:!0}),q("mousedown",K,t.current,z&&{passive:!0}),q("mouseup",D,t.current,z&&{passive:!0}),q("wheel",V,t.current,z&&{passive:!0}),q("resize",(function(){return m({height:window.innerHeight,width:window.innerWidth})}),window),{snapTo:Object(r.useCallback)((function(e,n){if(void 0===n&&(n=!1),n){var r=O.current[e]||O.current[0],o=r.top,i=r.left;t.current.scrollTo({top:o,left:i})}else T(O.current[e])}),[T,O]),isInteracting:g}}(c({},v,{scrollContainerRef:b,onSnapStart:Object(r.useCallback)((function(e){j!==S[e]&&k(S[e])}),[S,k]),onSnap:Object(r.useCallback)((function(){x.current=S.indexOf(j)}),[j])})),L=T.snapTo,_=T.isInteracting;Object(r.useLayoutEffect)((function(){m.current=L}),[L]),Object(r.useEffect)((function(){x.current>=0||(x.current=S.indexOf(j))}),[j]);var P=function(e,t,n,r,o){return r+((e=Math.min(n,Math.max(e,t)))-t)/(n-t)*(o-r)},M=function(e,t,n,r){var o=y.current.get(S[t]),i=o&&o[w.offsetLeft]||0,a=o&&o[w.offsetWidth]||0,c=y.current.get(S[n]),s=c&&c[w.offsetLeft],l=c&&c[w.offsetWidth],u=d.current;if(u&&(u.style[w.left]=P(e,0,1,i,s)+"px",u.style[w.width]=P(e,0,1,a,l)+"px","function"===typeof C.current)){var f=S.indexOf(j);_.current&&(x.current=f);var p=n-t;(p<0&&x.current<f||p>0&&x.current>f)&&(x.current=t);var v=_.current?n:f,h=_.current?t:x.current;h===f&&(h=n===f?t:n,v=n===f?n:t);var b=v-h,m=0===b?1:Math.abs((r-h)/b);m=Math.min(1,Math.max(m,0)),C.current({target:d.current.firstChild,progress:m,isInteracting:_.current})}};Object(r.useLayoutEffect)((function(){var e=S.indexOf(O);L(e,!0),M(1,e,e)}),[S,d]);var I=Object(r.useMemo)((function(){return t&&o.a.Children.map(t,(function(e){return o.a.isValidElement(e)&&"Pane"===e.props.__TYPE?o.a.cloneElement(e,{style:c({},i,e.props.style),className:[e.props.className,a].join(" ").trim()}):e}))}),[t,a]),R={position:"relative",display:"flex",flexDirection:g.flexDirection,flexGrow:"1",overflow:"auto"};return o.a.createElement("div",c({className:[z["tab-content"],l].join(" ").trim(),ref:b,onScroll:function(e){var t,n,r=Number(e.target.scrollLeft/e.target.clientWidth)||Number(e.target.scrollTop/e.target.clientHeight);E.current-r>0?(t=Math.ceil(r),n=Math.floor(r)):(n=Math.ceil(r),t=Math.floor(r));var o=Math.abs(t-r);o>1&&(o=1,t=n),E.current=r,M(o,t,n,r)},style:c({},R,n)},u),I)}function oe(e){var t=e.children,n=e.eventKey,i=s(e,U),a=Object(r.useRef)(null),l=Object(r.useContext)(G),u=l.eventHandler,f=l.events,p=l.snapTo,d=u[0],v=f[0];return Object(r.useEffect)((function(){v.length>0&&n===d&&p.current(v.indexOf(n))})),o.a.createElement("div",c({ref:a},i),t)}ee.propTypes={defaultKey:W.string,eventKeys:W.arrayOf(W.string),layout:W.string,snapDuration:W.number,easing:W.oneOfType([W.func,W.string]),indicatorClass:W.string,indicatorParentClass:W.string,indicatorStyle:W.object,indicatorParentStyle:W.object,indicatorSize:W.string,onIndicatorMove:W.func,activeLinkClass:W.string,activeLinkStyle:W.object,scrollIntoViewDuration:W.number,scrollIntoViewEasing:W.oneOfType([W.string,W.func]),scrollIntoViewOffset:W.number},te.propTypes={eventKeys:W.arrayOf(W.string),activeLinkClass:W.string,activeLinkStyle:W.object,indicatorColor:W.string,indicatorClass:W.string,indicatorSize:W.number,indicatorStyle:W.object,onIndicatorMove:W.func,linkStyle:W.object,linkClass:W.string,scrollIntoViewDuration:W.number,scrollIntoViewEasing:W.oneOfType([W.string,W.func]),scrollIntoViewOffset:W.number,__TYPE:W.string},te.defaultProps={__TYPE:"Nav"},ne.propTypes={eventKey:W.string,activeStyle:W.object,activeClass:W.string,__TYPE:W.string},ne.defaultProps={__TYPE:"Link"},re.propTypes={paneClass:W.string,paneStyle:W.object},oe.propTypes={eventKey:W.string,__TYPE:W.string},oe.defaultProps={__TYPE:"Pane"},ee.Nav=te,ee.Link=ne,ee.Content=re,ee.Pane=oe;var ie=ee,ae=(n(10),n(1),function(){return o.a.createElement(se,null)});function ce(e){var t=e.children,n=e.color;return o.a.createElement("div",{style:{backgroundColor:"transparent",display:"flex",justifyContent:"center",alignItems:"center",fontStyle:"bold",fontSize:"3vw",width:"100%",height:"100%",color:n}},t)}function se(){return o.a.createElement("div",{style:{width:"400px",height:"100vh",backgroundColor:"#333"}},o.a.createElement(ie,{style:{borderRight:"1px solid gray"},snapDuration:300,easing:"ease-out"},o.a.createElement(ie.Content,{paneStyle:{minHeight:"100%",minWidth:"100%"}},o.a.createElement(ie.Pane,{eventKey:"tab1"},o.a.createElement(ce,{color:"white"},"Content 1")),o.a.createElement(ie.Pane,{eventKey:"tab2"},o.a.createElement(ce,{color:"white"},"Content 2")),o.a.createElement(ie.Pane,{eventKey:"tab3"},o.a.createElement(ce,{color:"white"},"Content 3")),o.a.createElement(ie.Pane,{eventKey:"tab4"},o.a.createElement(ce,{color:"white"},"Content 4")),o.a.createElement(ie.Pane,{eventKey:"tab5"},o.a.createElement(ce,{color:"white"},"Content 5"))),o.a.createElement(ie.Nav,{activeLinkStyle:{color:"white"},linkStyle:{whiteSpace:"nowrap"},indicatorStyle:{borderRadius:"3px",width:"10px",maxWidth:"100%",backgroundColor:"orange"},style:{color:"gray",backgroundColor:"black",borderRadius:"5px"},onIndicatorMove:function(e){var t=e.target,n=function(e){return-12*(e-.5)*(e-.5)+4}(e.progress);t.style.width=10*n+"px"},className:"tab-nav"},o.a.createElement(ie.Link,{eventKey:"tab1"},"Tab 1"),o.a.createElement(ie.Link,{eventKey:"tab2"},"Very Long Tab 2"),o.a.createElement(ie.Link,{eventKey:"tab3"},"Tab 3"),o.a.createElement(ie.Link,{eventKey:"tab4"},"Very Long Tab 4"),o.a.createElement(ie.Link,{eventKey:"tab5"},"Very Long Tab 5"))))}a.a.render(o.a.createElement(ae,null),document.getElementById("root"))}],[[5,1,2]]]);
//# sourceMappingURL=main.d06247d9.chunk.js.map