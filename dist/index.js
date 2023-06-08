function _interopDefault (ex) { return (ex && (typeof ex === 'object') && 'default' in ex) ? ex['default'] : ex; }

var React = require('react');
var React__default = _interopDefault(React);

function _extends() {
  _extends = Object.assign ? Object.assign.bind() : function (target) {
    for (var i = 1; i < arguments.length; i++) {
      var source = arguments[i];
      for (var key in source) {
        if (Object.prototype.hasOwnProperty.call(source, key)) {
          target[key] = source[key];
        }
      }
    }
    return target;
  };
  return _extends.apply(this, arguments);
}
function _objectWithoutPropertiesLoose(source, excluded) {
  if (source == null) return {};
  var target = {};
  var sourceKeys = Object.keys(source);
  var key, i;
  for (i = 0; i < sourceKeys.length; i++) {
    key = sourceKeys[i];
    if (excluded.indexOf(key) >= 0) continue;
    target[key] = source[key];
  }
  return target;
}

function createCommonjsModule(fn, module) {
	return module = { exports: {} }, fn(module, module.exports), module.exports;
}

/** @license React v16.13.1
 * react-is.production.min.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */
var b="function"===typeof Symbol&&Symbol.for,c=b?Symbol.for("react.element"):60103,d=b?Symbol.for("react.portal"):60106,e=b?Symbol.for("react.fragment"):60107,f=b?Symbol.for("react.strict_mode"):60108,g=b?Symbol.for("react.profiler"):60114,h=b?Symbol.for("react.provider"):60109,k=b?Symbol.for("react.context"):60110,l=b?Symbol.for("react.async_mode"):60111,m=b?Symbol.for("react.concurrent_mode"):60111,n=b?Symbol.for("react.forward_ref"):60112,p=b?Symbol.for("react.suspense"):60113,q=b?
Symbol.for("react.suspense_list"):60120,r=b?Symbol.for("react.memo"):60115,t=b?Symbol.for("react.lazy"):60116,v=b?Symbol.for("react.block"):60121,w=b?Symbol.for("react.fundamental"):60117,x=b?Symbol.for("react.responder"):60118,y=b?Symbol.for("react.scope"):60119;
function z(a){if("object"===typeof a&&null!==a){var u=a.$$typeof;switch(u){case c:switch(a=a.type,a){case l:case m:case e:case g:case f:case p:return a;default:switch(a=a&&a.$$typeof,a){case k:case n:case t:case r:case h:return a;default:return u}}case d:return u}}}function A(a){return z(a)===m}var AsyncMode=l;var ConcurrentMode=m;var ContextConsumer=k;var ContextProvider=h;var Element=c;var ForwardRef=n;var Fragment=e;var Lazy=t;var Memo=r;var Portal=d;
var Profiler=g;var StrictMode=f;var Suspense=p;var isAsyncMode=function(a){return A(a)||z(a)===l};var isConcurrentMode=A;var isContextConsumer=function(a){return z(a)===k};var isContextProvider=function(a){return z(a)===h};var isElement=function(a){return "object"===typeof a&&null!==a&&a.$$typeof===c};var isForwardRef=function(a){return z(a)===n};var isFragment=function(a){return z(a)===e};var isLazy=function(a){return z(a)===t};
var isMemo=function(a){return z(a)===r};var isPortal=function(a){return z(a)===d};var isProfiler=function(a){return z(a)===g};var isStrictMode=function(a){return z(a)===f};var isSuspense=function(a){return z(a)===p};
var isValidElementType=function(a){return "string"===typeof a||"function"===typeof a||a===e||a===m||a===g||a===f||a===p||a===q||"object"===typeof a&&null!==a&&(a.$$typeof===t||a.$$typeof===r||a.$$typeof===h||a.$$typeof===k||a.$$typeof===n||a.$$typeof===w||a.$$typeof===x||a.$$typeof===y||a.$$typeof===v)};var typeOf=z;

var reactIs_production_min = {
	AsyncMode: AsyncMode,
	ConcurrentMode: ConcurrentMode,
	ContextConsumer: ContextConsumer,
	ContextProvider: ContextProvider,
	Element: Element,
	ForwardRef: ForwardRef,
	Fragment: Fragment,
	Lazy: Lazy,
	Memo: Memo,
	Portal: Portal,
	Profiler: Profiler,
	StrictMode: StrictMode,
	Suspense: Suspense,
	isAsyncMode: isAsyncMode,
	isConcurrentMode: isConcurrentMode,
	isContextConsumer: isContextConsumer,
	isContextProvider: isContextProvider,
	isElement: isElement,
	isForwardRef: isForwardRef,
	isFragment: isFragment,
	isLazy: isLazy,
	isMemo: isMemo,
	isPortal: isPortal,
	isProfiler: isProfiler,
	isStrictMode: isStrictMode,
	isSuspense: isSuspense,
	isValidElementType: isValidElementType,
	typeOf: typeOf
};

var reactIs_development = createCommonjsModule(function (module, exports) {



if (process.env.NODE_ENV !== "production") {
  (function() {

// The Symbol used to tag the ReactElement-like types. If there is no native Symbol
// nor polyfill, then a plain number is used for performance.
var hasSymbol = typeof Symbol === 'function' && Symbol.for;
var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace; // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
// (unstable) APIs that have been removed. Can we remove the symbols?

var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
var REACT_SUSPENSE_LIST_TYPE = hasSymbol ? Symbol.for('react.suspense_list') : 0xead8;
var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;
var REACT_BLOCK_TYPE = hasSymbol ? Symbol.for('react.block') : 0xead9;
var REACT_FUNDAMENTAL_TYPE = hasSymbol ? Symbol.for('react.fundamental') : 0xead5;
var REACT_RESPONDER_TYPE = hasSymbol ? Symbol.for('react.responder') : 0xead6;
var REACT_SCOPE_TYPE = hasSymbol ? Symbol.for('react.scope') : 0xead7;

function isValidElementType(type) {
  return typeof type === 'string' || typeof type === 'function' || // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
  type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || type === REACT_SUSPENSE_LIST_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE || type.$$typeof === REACT_FUNDAMENTAL_TYPE || type.$$typeof === REACT_RESPONDER_TYPE || type.$$typeof === REACT_SCOPE_TYPE || type.$$typeof === REACT_BLOCK_TYPE);
}

function typeOf(object) {
  if (typeof object === 'object' && object !== null) {
    var $$typeof = object.$$typeof;

    switch ($$typeof) {
      case REACT_ELEMENT_TYPE:
        var type = object.type;

        switch (type) {
          case REACT_ASYNC_MODE_TYPE:
          case REACT_CONCURRENT_MODE_TYPE:
          case REACT_FRAGMENT_TYPE:
          case REACT_PROFILER_TYPE:
          case REACT_STRICT_MODE_TYPE:
          case REACT_SUSPENSE_TYPE:
            return type;

          default:
            var $$typeofType = type && type.$$typeof;

            switch ($$typeofType) {
              case REACT_CONTEXT_TYPE:
              case REACT_FORWARD_REF_TYPE:
              case REACT_LAZY_TYPE:
              case REACT_MEMO_TYPE:
              case REACT_PROVIDER_TYPE:
                return $$typeofType;

              default:
                return $$typeof;
            }

        }

      case REACT_PORTAL_TYPE:
        return $$typeof;
    }
  }

  return undefined;
} // AsyncMode is deprecated along with isAsyncMode

var AsyncMode = REACT_ASYNC_MODE_TYPE;
var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
var ContextConsumer = REACT_CONTEXT_TYPE;
var ContextProvider = REACT_PROVIDER_TYPE;
var Element = REACT_ELEMENT_TYPE;
var ForwardRef = REACT_FORWARD_REF_TYPE;
var Fragment = REACT_FRAGMENT_TYPE;
var Lazy = REACT_LAZY_TYPE;
var Memo = REACT_MEMO_TYPE;
var Portal = REACT_PORTAL_TYPE;
var Profiler = REACT_PROFILER_TYPE;
var StrictMode = REACT_STRICT_MODE_TYPE;
var Suspense = REACT_SUSPENSE_TYPE;
var hasWarnedAboutDeprecatedIsAsyncMode = false; // AsyncMode should be deprecated

function isAsyncMode(object) {
  {
    if (!hasWarnedAboutDeprecatedIsAsyncMode) {
      hasWarnedAboutDeprecatedIsAsyncMode = true; // Using console['warn'] to evade Babel and ESLint

      console['warn']('The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
    }
  }

  return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
}
function isConcurrentMode(object) {
  return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
}
function isContextConsumer(object) {
  return typeOf(object) === REACT_CONTEXT_TYPE;
}
function isContextProvider(object) {
  return typeOf(object) === REACT_PROVIDER_TYPE;
}
function isElement(object) {
  return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
}
function isForwardRef(object) {
  return typeOf(object) === REACT_FORWARD_REF_TYPE;
}
function isFragment(object) {
  return typeOf(object) === REACT_FRAGMENT_TYPE;
}
function isLazy(object) {
  return typeOf(object) === REACT_LAZY_TYPE;
}
function isMemo(object) {
  return typeOf(object) === REACT_MEMO_TYPE;
}
function isPortal(object) {
  return typeOf(object) === REACT_PORTAL_TYPE;
}
function isProfiler(object) {
  return typeOf(object) === REACT_PROFILER_TYPE;
}
function isStrictMode(object) {
  return typeOf(object) === REACT_STRICT_MODE_TYPE;
}
function isSuspense(object) {
  return typeOf(object) === REACT_SUSPENSE_TYPE;
}

exports.AsyncMode = AsyncMode;
exports.ConcurrentMode = ConcurrentMode;
exports.ContextConsumer = ContextConsumer;
exports.ContextProvider = ContextProvider;
exports.Element = Element;
exports.ForwardRef = ForwardRef;
exports.Fragment = Fragment;
exports.Lazy = Lazy;
exports.Memo = Memo;
exports.Portal = Portal;
exports.Profiler = Profiler;
exports.StrictMode = StrictMode;
exports.Suspense = Suspense;
exports.isAsyncMode = isAsyncMode;
exports.isConcurrentMode = isConcurrentMode;
exports.isContextConsumer = isContextConsumer;
exports.isContextProvider = isContextProvider;
exports.isElement = isElement;
exports.isForwardRef = isForwardRef;
exports.isFragment = isFragment;
exports.isLazy = isLazy;
exports.isMemo = isMemo;
exports.isPortal = isPortal;
exports.isProfiler = isProfiler;
exports.isStrictMode = isStrictMode;
exports.isSuspense = isSuspense;
exports.isValidElementType = isValidElementType;
exports.typeOf = typeOf;
  })();
}
});

var reactIs = createCommonjsModule(function (module) {

if (process.env.NODE_ENV === 'production') {
  module.exports = reactIs_production_min;
} else {
  module.exports = reactIs_development;
}
});

/*
object-assign
(c) Sindre Sorhus
@license MIT
*/
/* eslint-disable no-unused-vars */
var getOwnPropertySymbols = Object.getOwnPropertySymbols;
var hasOwnProperty = Object.prototype.hasOwnProperty;
var propIsEnumerable = Object.prototype.propertyIsEnumerable;

function toObject(val) {
	if (val === null || val === undefined) {
		throw new TypeError('Object.assign cannot be called with null or undefined');
	}

	return Object(val);
}

function shouldUseNative() {
	try {
		if (!Object.assign) {
			return false;
		}

		// Detect buggy property enumeration order in older V8 versions.

		// https://bugs.chromium.org/p/v8/issues/detail?id=4118
		var test1 = new String('abc');  // eslint-disable-line no-new-wrappers
		test1[5] = 'de';
		if (Object.getOwnPropertyNames(test1)[0] === '5') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test2 = {};
		for (var i = 0; i < 10; i++) {
			test2['_' + String.fromCharCode(i)] = i;
		}
		var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
			return test2[n];
		});
		if (order2.join('') !== '0123456789') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test3 = {};
		'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
			test3[letter] = letter;
		});
		if (Object.keys(Object.assign({}, test3)).join('') !==
				'abcdefghijklmnopqrst') {
			return false;
		}

		return true;
	} catch (err) {
		// We don't expect any of the above to throw, but better to be safe.
		return false;
	}
}

var objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
	var from;
	var to = toObject(target);
	var symbols;

	for (var s = 1; s < arguments.length; s++) {
		from = Object(arguments[s]);

		for (var key in from) {
			if (hasOwnProperty.call(from, key)) {
				to[key] = from[key];
			}
		}

		if (getOwnPropertySymbols) {
			symbols = getOwnPropertySymbols(from);
			for (var i = 0; i < symbols.length; i++) {
				if (propIsEnumerable.call(from, symbols[i])) {
					to[symbols[i]] = from[symbols[i]];
				}
			}
		}
	}

	return to;
};

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

var ReactPropTypesSecret_1 = ReactPropTypesSecret;

var has = Function.call.bind(Object.prototype.hasOwnProperty);

var printWarning = function() {};

if (process.env.NODE_ENV !== 'production') {
  var ReactPropTypesSecret$1 = ReactPropTypesSecret_1;
  var loggedTypeFailures = {};
  var has$1 = has;

  printWarning = function(text) {
    var message = 'Warning: ' + text;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) { /**/ }
  };
}

/**
 * Assert that the values match with the type specs.
 * Error messages are memorized and will only be shown once.
 *
 * @param {object} typeSpecs Map of name to a ReactPropType
 * @param {object} values Runtime values that need to be type-checked
 * @param {string} location e.g. "prop", "context", "child context"
 * @param {string} componentName Name of the component for error messages.
 * @param {?Function} getStack Returns the component stack.
 * @private
 */
function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
  if (process.env.NODE_ENV !== 'production') {
    for (var typeSpecName in typeSpecs) {
      if (has$1(typeSpecs, typeSpecName)) {
        var error;
        // Prop type validation may throw. In case they do, we don't want to
        // fail the render phase where it didn't fail before. So we log it.
        // After these have been cleaned up, we'll let them throw.
        try {
          // This is intentionally an invariant that gets caught. It's the same
          // behavior as without this statement except with a better message.
          if (typeof typeSpecs[typeSpecName] !== 'function') {
            var err = Error(
              (componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' +
              'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.' +
              'This often happens because of typos such as `PropTypes.function` instead of `PropTypes.func`.'
            );
            err.name = 'Invariant Violation';
            throw err;
          }
          error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret$1);
        } catch (ex) {
          error = ex;
        }
        if (error && !(error instanceof Error)) {
          printWarning(
            (componentName || 'React class') + ': type specification of ' +
            location + ' `' + typeSpecName + '` is invalid; the type checker ' +
            'function must return `null` or an `Error` but returned a ' + typeof error + '. ' +
            'You may have forgotten to pass an argument to the type checker ' +
            'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
            'shape all require an argument).'
          );
        }
        if (error instanceof Error && !(error.message in loggedTypeFailures)) {
          // Only monitor this failure once because there tends to be a lot of the
          // same error.
          loggedTypeFailures[error.message] = true;

          var stack = getStack ? getStack() : '';

          printWarning(
            'Failed ' + location + ' type: ' + error.message + (stack != null ? stack : '')
          );
        }
      }
    }
  }
}

/**
 * Resets warning cache when testing.
 *
 * @private
 */
checkPropTypes.resetWarningCache = function() {
  if (process.env.NODE_ENV !== 'production') {
    loggedTypeFailures = {};
  }
};

var checkPropTypes_1 = checkPropTypes;

var printWarning$1 = function() {};

if (process.env.NODE_ENV !== 'production') {
  printWarning$1 = function(text) {
    var message = 'Warning: ' + text;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };
}

function emptyFunctionThatReturnsNull() {
  return null;
}

var factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
  /* global Symbol */
  var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
  var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

  /**
   * Returns the iterator method function contained on the iterable object.
   *
   * Be sure to invoke the function with the iterable as context:
   *
   *     var iteratorFn = getIteratorFn(myIterable);
   *     if (iteratorFn) {
   *       var iterator = iteratorFn.call(myIterable);
   *       ...
   *     }
   *
   * @param {?object} maybeIterable
   * @return {?function}
   */
  function getIteratorFn(maybeIterable) {
    var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
    if (typeof iteratorFn === 'function') {
      return iteratorFn;
    }
  }

  /**
   * Collection of methods that allow declaration and validation of props that are
   * supplied to React components. Example usage:
   *
   *   var Props = require('ReactPropTypes');
   *   var MyArticle = React.createClass({
   *     propTypes: {
   *       // An optional string prop named "description".
   *       description: Props.string,
   *
   *       // A required enum prop named "category".
   *       category: Props.oneOf(['News','Photos']).isRequired,
   *
   *       // A prop named "dialog" that requires an instance of Dialog.
   *       dialog: Props.instanceOf(Dialog).isRequired
   *     },
   *     render: function() { ... }
   *   });
   *
   * A more formal specification of how these methods are used:
   *
   *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
   *   decl := ReactPropTypes.{type}(.isRequired)?
   *
   * Each and every declaration produces a function with the same signature. This
   * allows the creation of custom validation functions. For example:
   *
   *  var MyLink = React.createClass({
   *    propTypes: {
   *      // An optional string or URI prop named "href".
   *      href: function(props, propName, componentName) {
   *        var propValue = props[propName];
   *        if (propValue != null && typeof propValue !== 'string' &&
   *            !(propValue instanceof URI)) {
   *          return new Error(
   *            'Expected a string or an URI for ' + propName + ' in ' +
   *            componentName
   *          );
   *        }
   *      }
   *    },
   *    render: function() {...}
   *  });
   *
   * @internal
   */

  var ANONYMOUS = '<<anonymous>>';

  // Important!
  // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
  var ReactPropTypes = {
    array: createPrimitiveTypeChecker('array'),
    bigint: createPrimitiveTypeChecker('bigint'),
    bool: createPrimitiveTypeChecker('boolean'),
    func: createPrimitiveTypeChecker('function'),
    number: createPrimitiveTypeChecker('number'),
    object: createPrimitiveTypeChecker('object'),
    string: createPrimitiveTypeChecker('string'),
    symbol: createPrimitiveTypeChecker('symbol'),

    any: createAnyTypeChecker(),
    arrayOf: createArrayOfTypeChecker,
    element: createElementTypeChecker(),
    elementType: createElementTypeTypeChecker(),
    instanceOf: createInstanceTypeChecker,
    node: createNodeChecker(),
    objectOf: createObjectOfTypeChecker,
    oneOf: createEnumTypeChecker,
    oneOfType: createUnionTypeChecker,
    shape: createShapeTypeChecker,
    exact: createStrictShapeTypeChecker,
  };

  /**
   * inlined Object.is polyfill to avoid requiring consumers ship their own
   * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
   */
  /*eslint-disable no-self-compare*/
  function is(x, y) {
    // SameValue algorithm
    if (x === y) {
      // Steps 1-5, 7-10
      // Steps 6.b-6.e: +0 != -0
      return x !== 0 || 1 / x === 1 / y;
    } else {
      // Step 6.a: NaN == NaN
      return x !== x && y !== y;
    }
  }
  /*eslint-enable no-self-compare*/

  /**
   * We use an Error-like object for backward compatibility as people may call
   * PropTypes directly and inspect their output. However, we don't use real
   * Errors anymore. We don't inspect their stack anyway, and creating them
   * is prohibitively expensive if they are created too often, such as what
   * happens in oneOfType() for any type before the one that matched.
   */
  function PropTypeError(message, data) {
    this.message = message;
    this.data = data && typeof data === 'object' ? data: {};
    this.stack = '';
  }
  // Make `instanceof Error` still work for returned errors.
  PropTypeError.prototype = Error.prototype;

  function createChainableTypeChecker(validate) {
    if (process.env.NODE_ENV !== 'production') {
      var manualPropTypeCallCache = {};
      var manualPropTypeWarningCount = 0;
    }
    function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
      componentName = componentName || ANONYMOUS;
      propFullName = propFullName || propName;

      if (secret !== ReactPropTypesSecret_1) {
        if (throwOnDirectAccess) {
          // New behavior only for users of `prop-types` package
          var err = new Error(
            'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
            'Use `PropTypes.checkPropTypes()` to call them. ' +
            'Read more at http://fb.me/use-check-prop-types'
          );
          err.name = 'Invariant Violation';
          throw err;
        } else if (process.env.NODE_ENV !== 'production' && typeof console !== 'undefined') {
          // Old behavior for people using React.PropTypes
          var cacheKey = componentName + ':' + propName;
          if (
            !manualPropTypeCallCache[cacheKey] &&
            // Avoid spamming the console because they are often not actionable except for lib authors
            manualPropTypeWarningCount < 3
          ) {
            printWarning$1(
              'You are manually calling a React.PropTypes validation ' +
              'function for the `' + propFullName + '` prop on `' + componentName + '`. This is deprecated ' +
              'and will throw in the standalone `prop-types` package. ' +
              'You may be seeing this warning due to a third-party PropTypes ' +
              'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.'
            );
            manualPropTypeCallCache[cacheKey] = true;
            manualPropTypeWarningCount++;
          }
        }
      }
      if (props[propName] == null) {
        if (isRequired) {
          if (props[propName] === null) {
            return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
          }
          return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
        }
        return null;
      } else {
        return validate(props, propName, componentName, location, propFullName);
      }
    }

    var chainedCheckType = checkType.bind(null, false);
    chainedCheckType.isRequired = checkType.bind(null, true);

    return chainedCheckType;
  }

  function createPrimitiveTypeChecker(expectedType) {
    function validate(props, propName, componentName, location, propFullName, secret) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== expectedType) {
        // `propValue` being instance of, say, date/regexp, pass the 'object'
        // check, but we can offer a more precise error message here rather than
        // 'of type `object`'.
        var preciseType = getPreciseType(propValue);

        return new PropTypeError(
          'Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'),
          {expectedType: expectedType}
        );
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createAnyTypeChecker() {
    return createChainableTypeChecker(emptyFunctionThatReturnsNull);
  }

  function createArrayOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
      }
      var propValue = props[propName];
      if (!Array.isArray(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
      }
      for (var i = 0; i < propValue.length; i++) {
        var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret_1);
        if (error instanceof Error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!isValidElement(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!reactIs.isValidElementType(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createInstanceTypeChecker(expectedClass) {
    function validate(props, propName, componentName, location, propFullName) {
      if (!(props[propName] instanceof expectedClass)) {
        var expectedClassName = expectedClass.name || ANONYMOUS;
        var actualClassName = getClassName(props[propName]);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createEnumTypeChecker(expectedValues) {
    if (!Array.isArray(expectedValues)) {
      if (process.env.NODE_ENV !== 'production') {
        if (arguments.length > 1) {
          printWarning$1(
            'Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' +
            'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
          );
        } else {
          printWarning$1('Invalid argument supplied to oneOf, expected an array.');
        }
      }
      return emptyFunctionThatReturnsNull;
    }

    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      for (var i = 0; i < expectedValues.length; i++) {
        if (is(propValue, expectedValues[i])) {
          return null;
        }
      }

      var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
        var type = getPreciseType(value);
        if (type === 'symbol') {
          return String(value);
        }
        return value;
      });
      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createObjectOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
      }
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
      }
      for (var key in propValue) {
        if (has(propValue, key)) {
          var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
          if (error instanceof Error) {
            return error;
          }
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createUnionTypeChecker(arrayOfTypeCheckers) {
    if (!Array.isArray(arrayOfTypeCheckers)) {
      process.env.NODE_ENV !== 'production' ? printWarning$1('Invalid argument supplied to oneOfType, expected an instance of array.') : void 0;
      return emptyFunctionThatReturnsNull;
    }

    for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
      var checker = arrayOfTypeCheckers[i];
      if (typeof checker !== 'function') {
        printWarning$1(
          'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
          'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.'
        );
        return emptyFunctionThatReturnsNull;
      }
    }

    function validate(props, propName, componentName, location, propFullName) {
      var expectedTypes = [];
      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
        var checker = arrayOfTypeCheckers[i];
        var checkerResult = checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret_1);
        if (checkerResult == null) {
          return null;
        }
        if (checkerResult.data && has(checkerResult.data, 'expectedType')) {
          expectedTypes.push(checkerResult.data.expectedType);
        }
      }
      var expectedTypesMessage = (expectedTypes.length > 0) ? ', expected one of type [' + expectedTypes.join(', ') + ']': '';
      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`' + expectedTypesMessage + '.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createNodeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      if (!isNode(props[propName])) {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function invalidValidatorError(componentName, location, propFullName, key, type) {
    return new PropTypeError(
      (componentName || 'React class') + ': ' + location + ' type `' + propFullName + '.' + key + '` is invalid; ' +
      'it must be a function, usually from the `prop-types` package, but received `' + type + '`.'
    );
  }

  function createShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      for (var key in shapeTypes) {
        var checker = shapeTypes[key];
        if (typeof checker !== 'function') {
          return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
        if (error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createStrictShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      // We need to check all keys in case some are required but missing from props.
      var allKeys = objectAssign({}, props[propName], shapeTypes);
      for (var key in allKeys) {
        var checker = shapeTypes[key];
        if (has(shapeTypes, key) && typeof checker !== 'function') {
          return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
        }
        if (!checker) {
          return new PropTypeError(
            'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
            '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
            '\nValid keys: ' + JSON.stringify(Object.keys(shapeTypes), null, '  ')
          );
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
        if (error) {
          return error;
        }
      }
      return null;
    }

    return createChainableTypeChecker(validate);
  }

  function isNode(propValue) {
    switch (typeof propValue) {
      case 'number':
      case 'string':
      case 'undefined':
        return true;
      case 'boolean':
        return !propValue;
      case 'object':
        if (Array.isArray(propValue)) {
          return propValue.every(isNode);
        }
        if (propValue === null || isValidElement(propValue)) {
          return true;
        }

        var iteratorFn = getIteratorFn(propValue);
        if (iteratorFn) {
          var iterator = iteratorFn.call(propValue);
          var step;
          if (iteratorFn !== propValue.entries) {
            while (!(step = iterator.next()).done) {
              if (!isNode(step.value)) {
                return false;
              }
            }
          } else {
            // Iterator will provide entry [k,v] tuples rather than values.
            while (!(step = iterator.next()).done) {
              var entry = step.value;
              if (entry) {
                if (!isNode(entry[1])) {
                  return false;
                }
              }
            }
          }
        } else {
          return false;
        }

        return true;
      default:
        return false;
    }
  }

  function isSymbol(propType, propValue) {
    // Native Symbol.
    if (propType === 'symbol') {
      return true;
    }

    // falsy value can't be a Symbol
    if (!propValue) {
      return false;
    }

    // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
    if (propValue['@@toStringTag'] === 'Symbol') {
      return true;
    }

    // Fallback for non-spec compliant Symbols which are polyfilled.
    if (typeof Symbol === 'function' && propValue instanceof Symbol) {
      return true;
    }

    return false;
  }

  // Equivalent of `typeof` but with special handling for array and regexp.
  function getPropType(propValue) {
    var propType = typeof propValue;
    if (Array.isArray(propValue)) {
      return 'array';
    }
    if (propValue instanceof RegExp) {
      // Old webkits (at least until Android 4.0) return 'function' rather than
      // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
      // passes PropTypes.object.
      return 'object';
    }
    if (isSymbol(propType, propValue)) {
      return 'symbol';
    }
    return propType;
  }

  // This handles more types than `getPropType`. Only used for error messages.
  // See `createPrimitiveTypeChecker`.
  function getPreciseType(propValue) {
    if (typeof propValue === 'undefined' || propValue === null) {
      return '' + propValue;
    }
    var propType = getPropType(propValue);
    if (propType === 'object') {
      if (propValue instanceof Date) {
        return 'date';
      } else if (propValue instanceof RegExp) {
        return 'regexp';
      }
    }
    return propType;
  }

  // Returns a string that is postfixed to a warning about an invalid type.
  // For example, "undefined" or "of type array"
  function getPostfixForTypeWarning(value) {
    var type = getPreciseType(value);
    switch (type) {
      case 'array':
      case 'object':
        return 'an ' + type;
      case 'boolean':
      case 'date':
      case 'regexp':
        return 'a ' + type;
      default:
        return type;
    }
  }

  // Returns class name of the object, if any.
  function getClassName(propValue) {
    if (!propValue.constructor || !propValue.constructor.name) {
      return ANONYMOUS;
    }
    return propValue.constructor.name;
  }

  ReactPropTypes.checkPropTypes = checkPropTypes_1;
  ReactPropTypes.resetWarningCache = checkPropTypes_1.resetWarningCache;
  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

function emptyFunction() {}
function emptyFunctionWithReset() {}
emptyFunctionWithReset.resetWarningCache = emptyFunction;

var factoryWithThrowingShims = function() {
  function shim(props, propName, componentName, location, propFullName, secret) {
    if (secret === ReactPropTypesSecret_1) {
      // It is still safe when called from React.
      return;
    }
    var err = new Error(
      'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
      'Use PropTypes.checkPropTypes() to call them. ' +
      'Read more at http://fb.me/use-check-prop-types'
    );
    err.name = 'Invariant Violation';
    throw err;
  }  shim.isRequired = shim;
  function getShim() {
    return shim;
  }  // Important!
  // Keep this list in sync with production version in `./factoryWithTypeCheckers.js`.
  var ReactPropTypes = {
    array: shim,
    bigint: shim,
    bool: shim,
    func: shim,
    number: shim,
    object: shim,
    string: shim,
    symbol: shim,

    any: shim,
    arrayOf: getShim,
    element: shim,
    elementType: shim,
    instanceOf: getShim,
    node: shim,
    objectOf: getShim,
    oneOf: getShim,
    oneOfType: getShim,
    shape: getShim,
    exact: getShim,

    checkPropTypes: emptyFunctionWithReset,
    resetWarningCache: emptyFunction
  };

  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

var propTypes = createCommonjsModule(function (module) {
/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

if (process.env.NODE_ENV !== 'production') {
  var ReactIs = reactIs;

  // By explicitly using `prop-types` you are opting into new development behavior.
  // http://fb.me/prop-types-in-prod
  var throwOnDirectAccess = true;
  module.exports = factoryWithTypeCheckers(ReactIs.isElement, throwOnDirectAccess);
} else {
  // By explicitly using `prop-types` you are opting into new production behavior.
  // http://fb.me/prop-types-in-prod
  module.exports = factoryWithThrowingShims();
}
});

var styles = {"tab-content":"_XaRX6","tab-nav":"_3vo4o"};

var defaultOptions = {
  duration: 300,
  easing: 'ease-out',
  fireAnimationEndEventOnStop: false
};
var Animation = /*#__PURE__*/function () {
  function Animation(options) {
    var _options = _extends({}, defaultOptions, options);
    switch (_options.easing) {
      case 'ease-in':
        _options.timing = function (t) {
          return t * t;
        };
        break;
      case 'ease-out':
        _options.timing = function (t) {
          return 1 - Math.pow(1 - t, 2);
        };
        break;
      case 'ease-in-out':
        _options.timing = function (t) {
          return t < 0.5 ? 2 * t * t : 1 - Math.pow(2 - 2 * t, 2) / 2;
        };
        break;
      default:
        if (typeof _options.easing === 'function') {
          _options.timing = _options.easing;
          break;
        }
        _options.timing = function (t) {
          return t;
        };
        break;
    }
    this.options = _options;
    this.stopped = true;
    this.started = false;
    this._events = {};
  }
  var _proto = Animation.prototype;
  _proto.start = function start() {
    var timing = this.options.timing;
    var update = this.options.update;
    var duration = this.options.duration;
    if (!window.requestAnimationFrame) {
      update(1);
      if (this._events['end']) {
        this._emit('end', this.progress);
      }
      console.warn('Your browser does not support window.requestAnimationFrame');
      return;
    }
    var startTime = window.performance.now();
    function _animate(time) {
      if (!this.started) {
        if (this._events['start']) this._emit('start');
        this.started = true;
      }
      if (this.stopped) {
        if (this._events['end'] && this.options.fireAnimationEndEventOnStop) this.emit('end', this.progress);
        return;
      }
      var timeFraction = (time - startTime) / duration;
      if (timeFraction < 0) {
        timeFraction = 0;
        startTime = time;
      }
      if (timeFraction > 1) {
        timeFraction = 1;
        this.stopped = true;
        if (this._events['end']) {
          this._emit('end', this.progress);
        }
      }
      var progress = timing(timeFraction);
      this.progress = progress;
      if (this.options.fromTo) {
        var fromTo = this.options.fromTo;
        var dist = fromTo[1] - fromTo[0];
        update(fromTo[0] + progress * dist);
      } else {
        update(progress);
      }
      if (timeFraction < 1) {
        this.requestId = window.requestAnimationFrame(_animate.bind(this));
      }
    }
    this.requestId = window.requestAnimationFrame(_animate.bind(this));
  };
  _proto.stop = function stop() {
    window.cancelAnimationFrame(this.requestId);
    this.stopped = true;
  };
  _proto.update = function update(callback) {
    this.options.update = callback;
    this.stopped = false;
    this.started = false;
    return this;
  };
  _proto.on = function on(name, callback) {
    if (!this._events[name]) {
      this._events[name] = [];
    }
    this._events[name].push(callback);
  };
  _proto.removeListener = function removeListener(name, callback) {
    if (!this._events[name]) return;
    var filterListeners = function filterListeners(listener) {
      return listener !== callback;
    };
    this._events[name] = this._events[name].filter(filterListeners);
  };
  _proto.removeAllListeners = function removeAllListeners() {
    this._events = {};
  };
  _proto._emit = function _emit(name, data) {
    if (!this._events[name]) {
      console.warn("Can't emit an event. Event \"" + name + "\" doesn't exits.");
      return;
    }
    this._events[name].forEach(function (callback) {
      callback(data);
    });
  };
  return Animation;
}();
var CONTAINER_INDEX = 0;
function useScrollSnap(_ref) {
  var scrollContainerRef = _ref.scrollContainerRef,
    _ref$childrenSelector = _ref.childrenSelector,
    childrenSelector = _ref$childrenSelector === void 0 ? '> div' : _ref$childrenSelector,
    _ref$threshold = _ref.threshold,
    threshold = _ref$threshold === void 0 ? 30 : _ref$threshold,
    _ref$swipeThreshold = _ref.swipeThreshold,
    swipeThreshold = _ref$swipeThreshold === void 0 ? 200 : _ref$swipeThreshold,
    _ref$easing = _ref.easing,
    easing = _ref$easing === void 0 ? 'ease-out' : _ref$easing,
    _ref$duration = _ref.duration,
    duration = _ref$duration === void 0 ? 250 : _ref$duration,
    onSnapStart = _ref.onSnapStart,
    onSnap = _ref.onSnap;
  var _useState = React.useState(null),
    windowDimension = _useState[0],
    setWindowDimension = _useState[1];
  var isInteracting = React.useRef(false);
  var animation = React.useRef(null);
  var snapPositionList = React.useRef([]);
  var activePosition = React.useRef();
  var index = React.useRef(null);
  var swipe = React.useRef(null);
  var scrollStart = React.useRef(null);
  var timeOut = React.useRef(null);
  React.useLayoutEffect(function () {
    index.current = CONTAINER_INDEX;
    scrollContainerRef.current.dataset.snapContainerId = index.current;
    scrollContainerRef.current.style.position = 'relative';
    animation.current = new Animation({
      easing: easing,
      duration: duration
    });
    CONTAINER_INDEX++;
  }, []);
  React.useLayoutEffect(function () {
    var reduceToSnapPositions = function reduceToSnapPositions(positions, child, i) {
      return [].concat(positions, [{
        index: i,
        top: child.offsetTop,
        left: child.offsetLeft,
        right: child.offsetLeft + child.offsetWidth,
        bottom: child.offsetTop + child.offsetHeight
      }]);
    };
    var query = "[data-snap-container-id=\"" + index.current + "\"] " + childrenSelector;
    snapPositionList.current = Array.from(scrollContainerRef.current.querySelectorAll(query)).reduce(reduceToSnapPositions, []);
    activePosition.current = snapPositionList.current[0];
  }, [childrenSelector, windowDimension]);
  var getScrollPosition = React.useCallback(function () {
    var container = scrollContainerRef.current;
    return {
      top: container.scrollTop,
      left: container.scrollLeft
    };
  }, []);
  var snapToDestination = React.useCallback(function (destination, currentPosition) {
    var _animation$current;
    if (!destination) return;
    currentPosition = currentPosition || getScrollPosition();
    var xDist = destination.left - currentPosition.left;
    var yDist = destination.top - currentPosition.top;
    if (xDist === 0 && yDist === 0 && destination.left === activePosition.current.left && destination.top === activePosition.current.top) {
      if (onSnapStart) onSnapStart(destination.index);
      activePosition.current = destination;
      return;
    }
    var draw = function draw(progress) {
      var left = currentPosition.left + progress * xDist;
      var top = currentPosition.top + progress * yDist;
      scrollContainerRef.current.scrollTo({
        top: top,
        left: left
      });
    };
    (_animation$current = animation.current) === null || _animation$current === void 0 ? void 0 : _animation$current.stop();
    animation.current.update(draw);
    animation.current.removeAllListeners();
    animation.current.on('start', function () {
      if (onSnapStart) onSnapStart(destination.index);
      activePosition.current = destination;
    });
    animation.current.on('end', function () {
      clearTimeout(timeOut.current);
      if (onSnap) onSnap(destination.index);
    });
    animation.current.start();
  }, [getScrollPosition, onSnapStart, onSnap]);
  var getPositionsInViewport = React.useCallback(function (container) {
    var scroll = getScrollPosition();
    var boundry = _extends({}, scroll, {
      right: scroll.left + container.clientWidth,
      bottom: scroll.top + container.clientHeight
    });
    return snapPositionList.current.filter(function (pos) {
      return pos.top < boundry.bottom && pos.bottom > boundry.top && pos.left < boundry.right && pos.right > boundry.left;
    });
  }, [getScrollPosition, snapPositionList]);
  var getSnapPosition = React.useCallback(function (deltaLeft, deltaTop) {
    var positionsInViewport = getPositionsInViewport(scrollContainerRef.current);
    var index = deltaLeft < 0 || deltaTop < 0 ? positionsInViewport[0].index + 1 : positionsInViewport[positionsInViewport.length - 1].index - 1;
    return snapPositionList.current[index] || positionsInViewport[0];
  }, [getPositionsInViewport]);
  var getNearestPositionInViewport = React.useCallback(function () {
    var positionsInViewport = getPositionsInViewport(scrollContainerRef.current);
    var scroll = getScrollPosition();
    if (positionsInViewport.length === 1) return positionsInViewport[0];
    return positionsInViewport.sort(function (a, b) {
      var leftCenter = (a.left + b.left) / 2;
      var topCenter = (a.top + b.top) / 2;
      var reverseFactor = a.left > b.left || a.top > b.top ? 1 : -1;
      return (leftCenter - scroll.left) * reverseFactor || (topCenter - scroll.top) * reverseFactor;
    })[0];
  }, [getPositionsInViewport, getScrollPosition]);
  var isSwipeTresholdExceeded = React.useCallback(function (deltaLeft, deltaTop) {
    if (Math.abs(deltaLeft) <= 5 && Math.abs(deltaTop) <= 5) return false;
    var calcWithInertia = function calcWithInertia() {
      var DEC = 625 * Math.pow(10, -6);
      var speed = swipe.current.xSpeed > swipe.current.ySpeed ? swipe.current.xSpeed : swipe.current.ySpeed;
      return speed * speed / (2 * DEC) > swipeThreshold;
    };
    return Math.abs(deltaTop) > swipeThreshold || Math.abs(deltaLeft) > swipeThreshold || calcWithInertia();
  }, [swipeThreshold]);
  var findAPositionAndSnap = React.useCallback(function () {
    var _scrollStart$current, _scrollStart$current2;
    if (!animation.current.stopped) return;
    var scroll = getScrollPosition();
    var deltaLeft = (((_scrollStart$current = scrollStart.current) === null || _scrollStart$current === void 0 ? void 0 : _scrollStart$current.left) || activePosition.current.left) - scroll.left;
    var deltaTop = (((_scrollStart$current2 = scrollStart.current) === null || _scrollStart$current2 === void 0 ? void 0 : _scrollStart$current2.top) || activePosition.current.top) - scroll.top;
    var destination;
    var tresholdExceeded = swipe.current ? isSwipeTresholdExceeded(deltaLeft, deltaTop) : Math.abs(deltaLeft) > threshold || Math.abs(deltaTop) > threshold;
    if (tresholdExceeded) {
      var snapPosition = getSnapPosition(deltaLeft, deltaTop);
      destination = snapPosition;
    } else {
      destination = getNearestPositionInViewport();
    }
    snapToDestination(destination, scroll);
  }, [getScrollPosition, isSwipeTresholdExceeded, threshold, getSnapPosition, snapToDestination]);
  var enableScroll = React.useCallback(function () {
    var container = scrollContainerRef.current;
    container.style.overflow = 'auto';
  }, []);
  var onScrollEnd = React.useCallback(function (time) {
    return function (e) {
      clearTimeout(timeOut.current);
      if (isInteracting.current || !animation.current.stopped) {
        return;
      }
      timeOut.current = setTimeout(function () {
        enableScroll();
        findAPositionAndSnap();
      }, time);
    };
  }, [enableScroll, findAPositionAndSnap]);
  var onInput = React.useCallback(function (e) {
    enableScroll();
    onScrollEnd(66)();
  }, [enableScroll, onScrollEnd]);
  var onInputStart = React.useCallback(function () {
    var _animation$current2;
    scrollStart.current = getScrollPosition();
    (_animation$current2 = animation.current) === null || _animation$current2 === void 0 ? void 0 : _animation$current2.stop();
    enableScroll();
    isInteracting.current = true;
  }, [enableScroll]);
  var onInputEnd = React.useCallback(function () {
    isInteracting.current = false;
    findAPositionAndSnap();
    scrollStart.current = null;
  }, [findAPositionAndSnap]);
  var onTouchStart = React.useCallback(function (e) {
    var touch = e.changedTouches[0];
    swipe.current = {};
    swipe.current.xStart = touch.clientX;
    swipe.current.yStart = touch.clientY;
    swipe.current.startTime = window.performance ? window.performance.now() : Date.now();
    onInputStart();
  }, [onInputStart]);
  var onTouchEnd = React.useCallback(function (e) {
    if (!swipe.current) return;
    var touch = e.changedTouches[0];
    var endTime = window.performance ? window.performance.now() : Date.now();
    var travelTime = endTime - swipe.current.startTime;
    swipe.current.xSpeed = Math.abs(swipe.current.xStart - touch.clientX) / travelTime;
    swipe.current.ySpeed = Math.abs(swipe.current.yStart - touch.clientY) / travelTime;
    var container = scrollContainerRef.current;
    container.style.overflow = 'hidden';
    onInputEnd();
    swipe.current = null;
  }, [onInputEnd]);
  var passiveSupported = React.useMemo(function () {
    var supported = false;
    try {
      var options = {
        get passive() {
          supported = true;
          return false;
        }
      };
      window.addEventListener('test', null, options);
      window.removeEventListener('test', null, options);
    } catch (err) {
      console.warn('window.addEventListener() does not support passive option');
    }
    return supported;
  });
  useEventListener('scroll', onScrollEnd(44), scrollContainerRef.current, passiveSupported && {
    passive: true
  });
  useEventListener('touchstart', onTouchStart, scrollContainerRef.current, passiveSupported && {
    passive: true
  });
  useEventListener('touchend', onTouchEnd, scrollContainerRef.current, passiveSupported && {
    passive: true
  });
  useEventListener('keydown', onInputStart, scrollContainerRef.current, passiveSupported && {
    passive: true
  });
  useEventListener('keyup', onInputEnd, scrollContainerRef.current, passiveSupported && {
    passive: true
  });
  useEventListener('mousedown', onInputStart, scrollContainerRef.current, passiveSupported && {
    passive: true
  });
  useEventListener('mouseup', onInputEnd, scrollContainerRef.current, passiveSupported && {
    passive: true
  });
  useEventListener('wheel', onInput, scrollContainerRef.current, passiveSupported && {
    passive: true
  });
  useEventListener('resize', function () {
    return setWindowDimension({
      height: window.innerHeight,
      width: window.innerWidth
    });
  }, window);
  var snapTo = React.useCallback(function (index, disableAnimation) {
    if (disableAnimation === void 0) {
      disableAnimation = false;
    }
    if (disableAnimation) {
      var _ref2 = snapPositionList.current[index] || snapPositionList.current[0],
        top = _ref2.top,
        left = _ref2.left;
      scrollContainerRef.current.scrollTo({
        top: top,
        left: left
      });
      return;
    }
    snapToDestination(snapPositionList.current[index]);
  }, [snapToDestination, snapPositionList]);
  return {
    snapTo: snapTo,
    isInteracting: isInteracting
  };
}
function useScrollIntoView(containerRef, duration, easing) {
  if (duration === void 0) {
    duration = 250;
  }
  if (easing === void 0) {
    easing = 'ease-out';
  }
  var animation = React.useRef(new Animation({
    duration: duration,
    easing: easing
  }));
  var getScrollPosition = React.useCallback(function () {
    var container = containerRef.current;
    return {
      top: container.scrollTop,
      left: container.scrollLeft
    };
  }, [containerRef]);
  var getBoundryBox = React.useCallback(function () {
    var container = containerRef.current;
    var scroll = getScrollPosition();
    return _extends({}, scroll, {
      bottom: scroll.top + container.clientHeight,
      right: scroll.left + container.clientWidth,
      scrollWidth: container.scrollWidth - container.clientWidth,
      scrollHeight: container.scrollHeight - container.clientHeight
    });
  }, [getScrollPosition, containerRef]);
  var getRelativeBoundryBox = React.useCallback(function (element) {
    return {
      left: element.offsetLeft,
      top: element.offsetTop,
      right: element.offsetLeft + element.offsetWidth,
      bottom: element.offsetTop + element.offsetHeight
    };
  }, []);
  var containsChild = React.useCallback(function (child) {
    var container = containerRef.current;
    if (window.document.contains) {
      return container.contains(child);
    }
    var node = child.parentNode;
    while (node != null) {
      if (node === container) {
        return true;
      }
      node = node.parentNode;
    }
    return false;
  }, [containerRef]);
  var scrollToDestination = React.useCallback(function (destination) {
    var container = containerRef.current;
    var scroll = getScrollPosition();
    var distX = destination.left - scroll.left;
    var distY = destination.top - scroll.top;
    var draw = function draw(progress) {
      container.scrollLeft = scroll.left + distX * progress;
      container.scrollTop = scroll.top + distY * progress;
    };
    animation.current.stop();
    animation.current.update(draw);
    animation.current.start();
  }, [getScrollPosition, containerRef]);
  return React.useCallback(function (element, offset) {
    if (!containsChild(element)) return;
    var OFFSET = {};
    OFFSET.x = typeof offset === 'object' ? Number(offset.x) || 0 : Number(offset) || 0;
    OFFSET.y = typeof offset === 'object' ? Number(offset.y) || 0 : Number(offset) || 0;
    var boundry = getBoundryBox();
    var childRect = getRelativeBoundryBox(element);
    var deltaX = childRect.left - OFFSET.x > boundry.left && childRect.right + OFFSET.x > boundry.right ? childRect.right - boundry.right + OFFSET.x : childRect.left - OFFSET.x < boundry.left && childRect.right + OFFSET.x < boundry.right ? childRect.left - boundry.left - OFFSET.x : 0;
    var deltaY = childRect.top > boundry.top && childRect.bottom > boundry.bottom ? childRect.bottom - boundry.bottom + OFFSET.y : childRect.top < boundry.top && childRect.bottom < boundry.bottom ? childRect.top - boundry.top - OFFSET.y : 0;
    var top = Math.max(0, Math.min(boundry.top + deltaY, boundry.scrollHeight));
    var left = Math.max(0, Math.min(boundry.left + deltaX, boundry.scrollWidth));
    var destination = {
      top: top,
      left: left
    };
    scrollToDestination(destination);
  }, [containsChild, getBoundryBox, getRelativeBoundryBox, scrollToDestination]);
}
function useEventListener(eventName, handler, element, options) {
  var _handler = React.useRef();
  React.useEffect(function () {
    _handler.current = handler;
  }, [handler]);
  React.useEffect(function () {
    var isHTMLElement = element && element.addEventListener;
    if (!isHTMLElement) return;
    var eventHandler = function eventHandler(e) {
      return _handler.current(e);
    };
    element.addEventListener(eventName, eventHandler, options);
    return function () {
      return element.removeEventListener(eventName, eventHandler, options);
    };
  }, [eventName, element]);
}

var _excluded = ["children", "defaultKey", "eventKeys", "style", "className", "layout", "snapDuration", "snapThreshold", "swipeThreshold", "easing", "indicatorClass", "indicatorColor", "indicatorStyle", "indicatorSize", "onIndicatorMove", "activeLinkClass", "activeLinkStyle", "indicatorParentStyle", "indicatorParentClass", "scrollIntoViewDuration", "scrollIntoViewEasing", "scrollIntoViewOffset", "linkStyle", "linkClass"],
  _excluded2 = ["eventKeys", "className", "activeLinkClass", "activeLinkStyle", "indicatorColor", "indicatorClass", "indicatorSize", "indicatorStyle", "onIndicatorMove", "indicatorParentStyle", "indicatorParentClass", "scrollIntoViewDuration", "scrollIntoViewEasing", "scrollIntoViewOffset", "children", "style", "linkStyle", "linkClass", "__TYPE"],
  _excluded3 = ["eventKey", "className", "children", "style", "activeStyle", "activeClass", "__TYPE"],
  _excluded4 = ["children", "style", "paneStyle", "paneClass", "className"],
  _excluded5 = ["children", "eventKey", "__TYPE"];
var TabProvider = React__default.createContext();
var LAYOUT_PROP_NAMES = {
  vertical: {
    left: 'left',
    width: 'width',
    offsetLeft: 'offsetLeft',
    offsetWidth: 'offsetWidth',
    minHeight: 'minHeight'
  },
  horizontal: {
    left: 'top',
    width: 'height',
    offsetLeft: 'offsetTop',
    offsetWidth: 'offsetHeight',
    minHeight: 'minWidth'
  }
};
var LAYOUT_PROP_VALUES = {
  vertical: {
    wrapperflexDirection: 'column',
    flexDirection: 'row',
    indicatorBottom: '0'
  },
  horizontal: {
    wrapperflexDirection: 'row',
    flexDirection: 'column',
    indicatorRight: '0'
  }
};
function ScrollSnapTabs(_ref) {
  var children = _ref.children,
    defaultKey = _ref.defaultKey,
    eventKeys = _ref.eventKeys,
    style = _ref.style,
    className = _ref.className,
    layout = _ref.layout,
    snapDuration = _ref.snapDuration,
    snapThreshold = _ref.snapThreshold,
    swipeThreshold = _ref.swipeThreshold,
    easing = _ref.easing,
    indicatorClass = _ref.indicatorClass,
    indicatorColor = _ref.indicatorColor,
    indicatorStyle = _ref.indicatorStyle,
    indicatorSize = _ref.indicatorSize,
    onIndicatorMove = _ref.onIndicatorMove,
    activeLinkClass = _ref.activeLinkClass,
    activeLinkStyle = _ref.activeLinkStyle,
    indicatorParentStyle = _ref.indicatorParentStyle,
    indicatorParentClass = _ref.indicatorParentClass,
    scrollIntoViewDuration = _ref.scrollIntoViewDuration,
    scrollIntoViewEasing = _ref.scrollIntoViewEasing,
    scrollIntoViewOffset = _ref.scrollIntoViewOffset,
    linkStyle = _ref.linkStyle,
    linkClass = _ref.linkClass,
    rest = _objectWithoutPropertiesLoose(_ref, _excluded);
  var propValues = layout === 'horizontal' ? LAYOUT_PROP_VALUES.horizontal : LAYOUT_PROP_VALUES.vertical;
  var propNames = layout === 'horizontal' ? LAYOUT_PROP_NAMES.horizontal : LAYOUT_PROP_NAMES.vertical;
  var _useState = React.useState(null),
    currentEvent = _useState[0],
    setCurrentEvent = _useState[1];
  var _useState2 = React.useState([]),
    events = _useState2[0],
    setEvents = _useState2[1];
  var indicatorRef = React.useRef(null);
  var onIndicatorMoveRef = React.useRef(onIndicatorMove);
  var contentRef = React.useRef(null);
  var snapTo = React.useRef(null);
  var linkMapRef = React.useRef(new Map());
  React.useEffect(function () {
    if (!currentEvent && events.length > 0) {
      setCurrentEvent(defaultKey || events[0]);
    }
  }, [events, setCurrentEvent]);
  return /*#__PURE__*/React__default.createElement(TabProvider.Provider, {
    value: {
      eventHandler: [currentEvent, setCurrentEvent],
      events: [events, setEvents],
      indicatorRef: indicatorRef,
      contentRef: contentRef,
      linkMapRef: linkMapRef,
      onIndicatorMoveRef: onIndicatorMoveRef,
      snapTo: snapTo,
      propValues: propValues,
      propNames: propNames,
      defaultKey: defaultKey || events[0],
      navOptions: {
        indicatorClass: indicatorClass,
        indicatorStyle: indicatorStyle,
        indicatorColor: indicatorColor,
        activeLinkClass: activeLinkClass,
        activeLinkStyle: activeLinkStyle,
        indicatorParentStyle: indicatorParentStyle,
        indicatorParentClass: indicatorParentClass,
        indicatorSize: indicatorSize,
        scrollIntoViewDuration: scrollIntoViewDuration,
        scrollIntoViewEasing: scrollIntoViewEasing,
        scrollIntoViewOffset: scrollIntoViewOffset,
        linkStyle: linkStyle,
        linkClass: linkClass
      },
      options: {
        duration: snapDuration,
        easing: easing,
        threshold: snapThreshold,
        swipeThreshold: swipeThreshold
      }
    }
  }, /*#__PURE__*/React__default.createElement("div", _extends({
    className: [styles.tabs, className].join(' ').trim(),
    style: _extends({
      display: 'flex',
      flexDirection: propValues.wrapperflexDirection,
      height: '100%',
      width: '100%'
    }, style)
  }, rest), eventKeys && /*#__PURE__*/React__default.createElement(Nav, {
    eventKeys: eventKeys
  }), children));
}
ScrollSnapTabs.propTypes = {
  defaultKey: propTypes.string,
  eventKeys: propTypes.arrayOf(propTypes.string),
  layout: propTypes.string,
  snapDuration: propTypes.number,
  easing: propTypes.oneOfType([propTypes.func, propTypes.string]),
  indicatorClass: propTypes.string,
  indicatorParentClass: propTypes.string,
  indicatorStyle: propTypes.object,
  indicatorParentStyle: propTypes.object,
  indicatorSize: propTypes.string,
  onIndicatorMove: propTypes.func,
  activeLinkClass: propTypes.string,
  activeLinkStyle: propTypes.object,
  scrollIntoViewDuration: propTypes.number,
  scrollIntoViewEasing: propTypes.oneOfType([propTypes.string, propTypes.func]),
  scrollIntoViewOffset: propTypes.number
};
function Nav(_ref2) {
  var _extends2;
  var eventKeys = _ref2.eventKeys,
    className = _ref2.className,
    activeLinkClass = _ref2.activeLinkClass,
    activeLinkStyle = _ref2.activeLinkStyle,
    indicatorColor = _ref2.indicatorColor,
    indicatorClass = _ref2.indicatorClass,
    indicatorSize = _ref2.indicatorSize,
    indicatorStyle = _ref2.indicatorStyle,
    onIndicatorMove = _ref2.onIndicatorMove,
    indicatorParentStyle = _ref2.indicatorParentStyle,
    indicatorParentClass = _ref2.indicatorParentClass,
    scrollIntoViewDuration = _ref2.scrollIntoViewDuration,
    scrollIntoViewEasing = _ref2.scrollIntoViewEasing,
    scrollIntoViewOffset = _ref2.scrollIntoViewOffset,
    children = _ref2.children,
    style = _ref2.style,
    linkStyle = _ref2.linkStyle,
    linkClass = _ref2.linkClass,
    rest = _objectWithoutPropertiesLoose(_ref2, _excluded2);
  var _useContext = React.useContext(TabProvider),
    indicatorRef = _useContext.indicatorRef,
    propValues = _useContext.propValues,
    propNames = _useContext.propNames,
    navOptions = _useContext.navOptions,
    linkMapRef = _useContext.linkMapRef,
    eventHandler = _useContext.eventHandler,
    onIndicatorMoveRef = _useContext.onIndicatorMoveRef,
    layout = _useContext.layout;
  var navContainerRef = React.useRef();
  var currentEvent = eventHandler[0];
  var scrollIntoRelativeView = useScrollIntoView(navContainerRef, scrollIntoViewDuration || navOptions.scrollIntoViewDuration, scrollIntoViewEasing || navOptions.scrollIntoViewEasing);
  var createNavLinks = function createNavLinks(event, i) {
    return /*#__PURE__*/React__default.createElement(Link, {
      key: i,
      eventKey: event,
      style: _extends({}, navOptions.linkStyle, linkStyle),
      className: linkClass || navOptions.linkClass,
      activeStyle: _extends({
        color: '#5A90E4'
      }, navOptions.activeLinkStyle, activeLinkStyle),
      activeClass: activeLinkClass || navOptions.activeLinkClass
    });
  };
  React.useLayoutEffect(function () {
    if (typeof onIndicatorMove === 'function') onIndicatorMoveRef.current = onIndicatorMove;
  }, []);
  React.useEffect(function () {
    scrollIntoRelativeView(linkMapRef.current.get(currentEvent), scrollIntoViewOffset || navOptions.scrollIntoViewOffset || 100);
  }, [currentEvent, scrollIntoRelativeView, scrollIntoViewOffset]);
  var _children = React.useMemo(function () {
    return children && React__default.Children.map(children, function (child) {
      if (React__default.isValidElement(child) && child.props.__TYPE === 'Link') {
        return React__default.cloneElement(child, {
          style: _extends({}, linkStyle, navOptions.linkStyle, child.props.style),
          className: [child.props.className, linkClass, navOptions.linkClass].join(' ').trim(),
          activeClass: child.props.activeClass || activeLinkClass || navOptions.activeLinkClass,
          activeStyle: _extends({}, navOptions.activeLinkStyle, activeLinkStyle, child.props.activeStyle)
        });
      }
      return child;
    });
  }, [children, activeLinkClass]);
  var defaultStyle = {
    display: 'flex',
    flexDirection: propValues.flexDirection,
    position: 'relative',
    overflow: 'auto',
    scrollbarWidth: 'none'
  };
  return /*#__PURE__*/React__default.createElement("div", _extends({
    ref: navContainerRef,
    style: _extends({}, style, defaultStyle),
    className: [styles['tab-nav'], className].join(' ').trim()
  }, rest), _children || eventKeys && eventKeys.map(createNavLinks), /*#__PURE__*/React__default.createElement("div", {
    style: _extends({
      position: 'absolute',
      bottom: propValues.indicatorBottom,
      right: propValues.indicatorRight
    }, navOptions.indicatorParentStyle, indicatorParentStyle),
    className: indicatorParentClass || navOptions.indicatorParentClass,
    ref: indicatorRef
  }, /*#__PURE__*/React__default.createElement("div", {
    className: indicatorClass || navOptions.indicatorClass || '',
    style: _extends((_extends2 = {
      width: layout === 'horizontal' ? '100%' : indicatorSize || navOptions.indicatorSize,
      height: layout === 'horizontal' ? indicatorSize || navOptions.indicatorSize : '100%',
      margin: 'auto '
    }, _extends2[propNames.minHeight] = '3px', _extends2.backgroundColor = indicatorColor || navOptions.indicatorColor || 'black', _extends2), navOptions.indicatorStyle, indicatorStyle)
  })));
}
Nav.propTypes = {
  eventKeys: propTypes.arrayOf(propTypes.string),
  activeLinkClass: propTypes.string,
  activeLinkStyle: propTypes.object,
  indicatorColor: propTypes.string,
  indicatorClass: propTypes.string,
  indicatorSize: propTypes.number,
  indicatorStyle: propTypes.object,
  onIndicatorMove: propTypes.func,
  linkStyle: propTypes.object,
  linkClass: propTypes.string,
  scrollIntoViewDuration: propTypes.number,
  scrollIntoViewEasing: propTypes.oneOfType([propTypes.string, propTypes.func]),
  scrollIntoViewOffset: propTypes.number,
  __TYPE: propTypes.string
};
Nav.defaultProps = {
  __TYPE: 'Nav'
};
function Link(_ref3) {
  var eventKey = _ref3.eventKey,
    className = _ref3.className,
    children = _ref3.children,
    style = _ref3.style,
    activeStyle = _ref3.activeStyle,
    activeClass = _ref3.activeClass,
    rest = _objectWithoutPropertiesLoose(_ref3, _excluded3);
  var _useContext2 = React.useContext(TabProvider),
    eventHandler = _useContext2.eventHandler,
    events = _useContext2.events,
    linkMapRef = _useContext2.linkMapRef;
  var selectedTab = eventHandler[0],
    setSelectedTab = eventHandler[1];
  var setLinks = events[1];
  var linkRef = React.useRef(null);
  var handleClick = function handleClick(e) {
    setSelectedTab(eventKey);
  };
  React.useLayoutEffect(function () {
    setLinks(function (prev) {
      return [].concat(prev, [eventKey]);
    });
    linkMapRef.current.set(eventKey, linkRef.current);
  }, [eventKey, setLinks]);
  var _className = selectedTab === eventKey ? [className, activeClass].join(' ').trim() : className;
  var defaultStyle = _extends({
    cursor: 'pointer',
    padding: '0.5rem'
  }, style);
  return /*#__PURE__*/React__default.createElement("div", _extends({
    onClick: handleClick,
    className: _className,
    style: selectedTab === eventKey ? _extends({}, defaultStyle, activeStyle) : defaultStyle,
    ref: linkRef
  }, rest), children || eventKey);
}
Link.propTypes = {
  eventKey: propTypes.string,
  activeStyle: propTypes.object,
  activeClass: propTypes.string,
  __TYPE: propTypes.string
};
Link.defaultProps = {
  __TYPE: 'Link'
};
function Content(_ref4) {
  var children = _ref4.children,
    style = _ref4.style,
    paneStyle = _ref4.paneStyle,
    paneClass = _ref4.paneClass,
    className = _ref4.className,
    rest = _objectWithoutPropertiesLoose(_ref4, _excluded4);
  var _useContext3 = React.useContext(TabProvider),
    eventHandler = _useContext3.eventHandler,
    indicatorRef = _useContext3.indicatorRef,
    options = _useContext3.options,
    events = _useContext3.events,
    linkMapRef = _useContext3.linkMapRef,
    contentRef = _useContext3.contentRef,
    _snapTo = _useContext3.snapTo,
    propValues = _useContext3.propValues,
    propNames = _useContext3.propNames,
    defaultKey = _useContext3.defaultKey,
    onIndicatorMoveRef = _useContext3.onIndicatorMoveRef;
  var links = events[0];
  var currentEvent = eventHandler[0],
    setCurrentEvent = eventHandler[1];
  var prevScroll = React.useRef(null);
  var prevEventIndex = React.useRef(events.indexOf(currentEvent));
  var onSnapStart = React.useCallback(function (index) {
    if (currentEvent === links[index]) return;
    setCurrentEvent(links[index]);
  }, [links, setCurrentEvent]);
  var onSnap = React.useCallback(function () {
    prevEventIndex.current = links.indexOf(currentEvent);
  }, [currentEvent]);
  var _useScrollSnap = useScrollSnap(_extends({}, options, {
      scrollContainerRef: contentRef,
      onSnapStart: onSnapStart,
      onSnap: onSnap
    })),
    snapTo = _useScrollSnap.snapTo,
    isInteracting = _useScrollSnap.isInteracting;
  React.useLayoutEffect(function () {
    _snapTo.current = snapTo;
  }, [snapTo]);
  React.useEffect(function () {
    if (prevEventIndex.current >= 0) return;
    prevEventIndex.current = links.indexOf(currentEvent);
  }, [currentEvent]);
  var mapNumber = function mapNumber(number, numberMin, numberMax, mapFrom, mapTo) {
    number = Math.min(numberMax, Math.max(number, numberMin));
    return mapFrom + (number - numberMin) / (numberMax - numberMin) * (mapTo - mapFrom);
  };
  var moveIndicator = function moveIndicator(progress, prevIndex, direction, scrollValue) {
    var current = linkMapRef.current.get(links[prevIndex]);
    var currentLeft = current && current[propNames.offsetLeft] || 0;
    var currentWidth = current && current[propNames.offsetWidth] || 0;
    var target = linkMapRef.current.get(links[direction]);
    var targetLeft = target && target[propNames.offsetLeft];
    var targetWidth = target && target[propNames.offsetWidth];
    var indicator = indicatorRef.current;
    if (!indicator) return;
    indicator.style[propNames.left] = mapNumber(progress, 0, 1, currentLeft, targetLeft) + 'px';
    indicator.style[propNames.width] = mapNumber(progress, 0, 1, currentWidth, targetWidth) + 'px';
    if (typeof onIndicatorMoveRef.current === 'function') {
      var activeIndex = links.indexOf(currentEvent);
      if (isInteracting.current) {
        prevEventIndex.current = activeIndex;
      }
      var movementDir = direction - prevIndex;
      if (movementDir < 0 && prevEventIndex.current < activeIndex || movementDir > 0 && prevEventIndex.current > activeIndex) {
        prevEventIndex.current = prevIndex;
      }
      var _targetIndex = isInteracting.current ? direction : activeIndex;
      var _prevIndex = isInteracting.current ? prevIndex : prevEventIndex.current;
      if (_prevIndex === activeIndex) {
        _prevIndex = direction === activeIndex ? prevIndex : direction;
        _targetIndex = direction === activeIndex ? direction : prevIndex;
      }
      var delta = _targetIndex - _prevIndex;
      var _progress = delta === 0 ? 1 : Math.abs((scrollValue - _prevIndex) / delta);
      _progress = Math.min(1, Math.max(_progress, 0));
      onIndicatorMoveRef.current({
        target: indicatorRef.current.firstChild,
        progress: _progress,
        isInteracting: isInteracting.current
      });
    }
  };
  var handleScroll = function handleScroll(e) {
    var prevIndex, direction;
    var scrollValue = Number(e.target.scrollLeft / e.target.clientWidth) || Number(e.target.scrollTop / e.target.clientHeight);
    if (prevScroll.current - scrollValue > 0) {
      prevIndex = Math.ceil(scrollValue);
      direction = Math.floor(scrollValue);
    } else {
      direction = Math.ceil(scrollValue);
      prevIndex = Math.floor(scrollValue);
    }
    var unitScroll = Math.abs(prevIndex - scrollValue);
    if (unitScroll > 1) {
      unitScroll = 1;
      prevIndex = direction;
    }
    prevScroll.current = scrollValue;
    moveIndicator(unitScroll, prevIndex, direction, scrollValue);
  };
  React.useLayoutEffect(function () {
    var currIndex = links.indexOf(defaultKey);
    snapTo(currIndex, true);
    moveIndicator(1, currIndex, currIndex);
  }, [links, indicatorRef]);
  var _children = React.useMemo(function () {
    return children && React__default.Children.map(children, function (child) {
      if (React__default.isValidElement(child) && child.props.__TYPE === 'Pane') {
        return React__default.cloneElement(child, {
          style: _extends({}, paneStyle, child.props.style),
          className: [child.props.className, paneClass].join(' ').trim()
        });
      }
      return child;
    });
  }, [children, paneClass]);
  var defaultStyle = {
    position: 'relative',
    display: 'flex',
    flexDirection: propValues.flexDirection,
    flexGrow: '1',
    overflow: 'auto',
    WebkitOverFlowScrolling: 'auto'
  };
  return /*#__PURE__*/React__default.createElement("div", _extends({
    className: [styles['tab-content'], className].join(' ').trim(),
    ref: contentRef,
    onScroll: handleScroll,
    style: _extends({}, defaultStyle, style)
  }, rest), _children);
}
Content.propTypes = {
  paneClass: propTypes.string,
  paneStyle: propTypes.object
};
function Pane(_ref5) {
  var children = _ref5.children,
    eventKey = _ref5.eventKey,
    rest = _objectWithoutPropertiesLoose(_ref5, _excluded5);
  var paneRef = React.useRef(null);
  var _useContext4 = React.useContext(TabProvider),
    eventHandler = _useContext4.eventHandler,
    events = _useContext4.events,
    snapTo = _useContext4.snapTo;
  var currentEvent = eventHandler[0];
  var links = events[0];
  React.useEffect(function () {
    if (links.length > 0 && eventKey === currentEvent) snapTo.current(links.indexOf(eventKey));
  });
  return /*#__PURE__*/React__default.createElement("div", _extends({
    ref: paneRef
  }, rest), children);
}
Pane.propTypes = {
  eventKey: propTypes.string,
  __TYPE: propTypes.string
};
Pane.defaultProps = {
  __TYPE: 'Pane'
};
ScrollSnapTabs.Nav = Nav;
ScrollSnapTabs.Link = Link;
ScrollSnapTabs.Content = Content;
ScrollSnapTabs.Pane = Pane;

module.exports = ScrollSnapTabs;
//# sourceMappingURL=index.js.map
