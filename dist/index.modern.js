import React, { useCallback, useRef, useState, useLayoutEffect, useMemo, useEffect, useContext } from 'react';

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

var styles = {"tab-content":"_styles-module__tab-content__XaRX6","tab-nav":"_styles-module__tab-nav__3vo4o"};

const defaultOptions = {
  duration: 300,
  easing: 'ease-out',
  fireAnimationEndEventOnStop: false
};
class Animation {
  constructor(options) {
    const _options = {
      ...defaultOptions,
      ...options
    };
    switch (_options.easing) {
      case 'ease-in':
        _options.timing = t => t * t;
        break;
      case 'ease-out':
        _options.timing = t => 1 - Math.pow(1 - t, 2);
        break;
      case 'ease-in-out':
        _options.timing = t => t < 0.5 ? 2 * t * t : 1 - Math.pow(2 - 2 * t, 2) / 2;
        break;
      default:
        if (typeof _options.easing === 'function') {
          _options.timing = _options.easing;
          break;
        }
        _options.timing = t => t;
        break;
    }
    this.options = _options;
    this.stopped = true;
    this.started = false;
    this._events = {};
  }
  start() {
    const timing = this.options.timing;
    const update = this.options.update;
    const duration = this.options.duration;
    if (!window.requestAnimationFrame) {
      update(1);
      if (this._events['end']) {
        this._emit('end', this.progress);
      }
      console.warn('Your browser does not support window.requestAnimationFrame');
      return;
    }
    let startTime = window.performance.now();
    function _animate(time) {
      if (!this.started) {
        if (this._events['start']) this._emit('start');
        this.started = true;
      }
      if (this.stopped) {
        if (this._events['end'] && this.options.fireAnimationEndEventOnStop) this.emit('end', this.progress);
        return;
      }
      let timeFraction = (time - startTime) / duration;
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
      const progress = timing(timeFraction);
      this.progress = progress;
      if (this.options.fromTo) {
        const fromTo = this.options.fromTo;
        const dist = fromTo[1] - fromTo[0];
        update(fromTo[0] + progress * dist);
      } else {
        update(progress);
      }
      if (timeFraction < 1) {
        this.requestId = window.requestAnimationFrame(_animate.bind(this));
      }
    }
    this.requestId = window.requestAnimationFrame(_animate.bind(this));
  }
  stop() {
    window.cancelAnimationFrame(this.requestId);
    this.stopped = true;
  }
  update(callback) {
    this.options.update = callback;
    this.stopped = false;
    this.started = false;
    return this;
  }
  on(name, callback) {
    if (!this._events[name]) {
      this._events[name] = [];
    }
    this._events[name].push(callback);
  }
  removeListener(name, callback) {
    if (!this._events[name]) return;
    const filterListeners = listener => listener !== callback;
    this._events[name] = this._events[name].filter(filterListeners);
  }
  removeAllListeners() {
    this._events = {};
  }
  _emit(name, data) {
    if (!this._events[name]) {
      console.warn(`Can't emit an event. Event "${name}" doesn't exits.`);
      return;
    }
    this._events[name].forEach(callback => {
      callback(data);
    });
  }
}
let CONTAINER_INDEX = 0;
function useScrollSnap({
  scrollContainerRef,
  childrenSelector = '> div',
  threshold = 30,
  swipeThreshold = 200,
  easing = 'ease-out',
  duration = 250,
  onSnapStart,
  onSnap
}) {
  const [windowSize, setWindowSize] = useState(null);
  const isInteracting = useRef(false);
  const animation = useRef(null);
  const snapPositionList = useRef([]);
  const activePosition = useRef();
  const index = useRef(null);
  const swipe = useRef(null);
  const scrollStart = useRef(null);
  const timeOut = useRef(null);
  useLayoutEffect(() => {
    index.current = CONTAINER_INDEX;
    scrollContainerRef.current.dataset.snapContainerId = index.current;
    scrollContainerRef.current.style.position = 'relative';
    animation.current = new Animation({
      easing,
      duration
    });
    CONTAINER_INDEX++;
  }, []);
  useLayoutEffect(() => {
    const reduceToSnapPositions = (positions, child, i) => [...positions, {
      index: i,
      top: child.offsetTop,
      left: child.offsetLeft,
      right: child.offsetLeft + child.offsetWidth,
      bottom: child.offsetTop + child.offsetHeight
    }];
    const query = `[data-snap-container-id="${index.current}"] ${childrenSelector}`;
    snapPositionList.current = Array.from(scrollContainerRef.current.querySelectorAll(query)).reduce(reduceToSnapPositions, []);
    if (!activePosition.current || !scrollContainerRef.current) return;
    const container = scrollContainerRef.current;
    activePosition.current = snapPositionList.current[activePosition.current.index];
    container.scrollLeft = activePosition.current.left;
    container.scrollTop = activePosition.current.top;
  }, [childrenSelector, windowSize]);
  useLayoutEffect(() => {
    activePosition.current = snapPositionList.current[0];
  }, []);
  const getScrollPosition = useCallback(() => {
    const container = scrollContainerRef.current;
    return {
      top: container.scrollTop,
      left: container.scrollLeft
    };
  }, []);
  const snapToDestination = useCallback((destination, currentPosition) => {
    var _animation$current;
    if (!destination) return;
    currentPosition = currentPosition || getScrollPosition();
    const xDist = destination.left - currentPosition.left;
    const yDist = destination.top - currentPosition.top;
    if (xDist === 0 && yDist === 0 && destination.left === activePosition.current.left && destination.top === activePosition.current.top) {
      if (onSnapStart) onSnapStart(destination.index);
      activePosition.current = destination;
      return;
    }
    const draw = progress => {
      const left = currentPosition.left + progress * xDist;
      const top = currentPosition.top + progress * yDist;
      scrollContainerRef.current.scrollTo({
        top,
        left
      });
    };
    (_animation$current = animation.current) === null || _animation$current === void 0 ? void 0 : _animation$current.stop();
    animation.current.update(draw);
    animation.current.removeAllListeners();
    animation.current.on('start', () => {
      if (onSnapStart) onSnapStart(destination.index);
      activePosition.current = destination;
    });
    animation.current.on('end', () => {
      clearTimeout(timeOut.current);
      if (onSnap) onSnap(destination.index);
    });
    animation.current.start();
  }, [getScrollPosition, onSnapStart, onSnap]);
  const getPositionsInViewport = useCallback(container => {
    const scroll = getScrollPosition();
    const boundry = {
      ...scroll,
      right: scroll.left + container.clientWidth,
      bottom: scroll.top + container.clientHeight
    };
    return snapPositionList.current.filter(pos => {
      return pos.top < boundry.bottom && pos.bottom > boundry.top && pos.left < boundry.right && pos.right > boundry.left;
    });
  }, [getScrollPosition, snapPositionList]);
  const getSnapPosition = useCallback((deltaLeft, deltaTop) => {
    const positionsInViewport = getPositionsInViewport(scrollContainerRef.current);
    const index = deltaLeft < 0 || deltaTop < 0 ? positionsInViewport[0].index + 1 : positionsInViewport[positionsInViewport.length - 1].index - 1;
    return snapPositionList.current[index] || positionsInViewport[0];
  }, [getPositionsInViewport]);
  const getNearestPositionInViewport = useCallback(() => {
    const positionsInViewport = getPositionsInViewport(scrollContainerRef.current);
    const scroll = getScrollPosition();
    if (positionsInViewport.length === 1) return positionsInViewport[0];
    return positionsInViewport.sort((a, b) => {
      const leftCenter = (a.left + b.left) / 2;
      const topCenter = (a.top + b.top) / 2;
      const reverseFactor = a.left > b.left || a.top > b.top ? 1 : -1;
      return (leftCenter - scroll.left) * reverseFactor || (topCenter - scroll.top) * reverseFactor;
    })[0];
  }, [getPositionsInViewport, getScrollPosition]);
  const isSwipeTresholdExceeded = useCallback((deltaLeft, deltaTop) => {
    if (Math.abs(deltaLeft) <= 5 && Math.abs(deltaTop) <= 5) return false;
    const calcWithInertia = () => {
      const DEC = 625 * Math.pow(10, -6);
      const speed = swipe.current.xSpeed > swipe.current.ySpeed ? swipe.current.xSpeed : swipe.current.ySpeed;
      return speed * speed / (2 * DEC) > swipeThreshold;
    };
    return Math.abs(deltaTop) > swipeThreshold || Math.abs(deltaLeft) > swipeThreshold || calcWithInertia();
  }, [swipeThreshold]);
  const findAPositionAndSnap = useCallback(() => {
    var _scrollStart$current, _scrollStart$current2;
    if (!animation.current.stopped) return;
    const scroll = getScrollPosition();
    const deltaLeft = (((_scrollStart$current = scrollStart.current) === null || _scrollStart$current === void 0 ? void 0 : _scrollStart$current.left) || activePosition.current.left) - scroll.left;
    const deltaTop = (((_scrollStart$current2 = scrollStart.current) === null || _scrollStart$current2 === void 0 ? void 0 : _scrollStart$current2.top) || activePosition.current.top) - scroll.top;
    let destination;
    const tresholdExceeded = swipe.current ? isSwipeTresholdExceeded(deltaLeft, deltaTop) : Math.abs(deltaLeft) > threshold || Math.abs(deltaTop) > threshold;
    if (tresholdExceeded) {
      const snapPosition = getSnapPosition(deltaLeft, deltaTop);
      destination = snapPosition;
    } else {
      destination = getNearestPositionInViewport();
    }
    snapToDestination(destination, scroll);
  }, [getScrollPosition, isSwipeTresholdExceeded, threshold, getSnapPosition, snapToDestination]);
  const enableScroll = useCallback(() => {
    const container = scrollContainerRef.current;
    container.style.overflow = 'auto';
  }, []);
  const onScrollEnd = useCallback(time => {
    return e => {
      clearTimeout(timeOut.current);
      if (isInteracting.current || !animation.current.stopped) {
        return;
      }
      timeOut.current = setTimeout(() => {
        enableScroll();
        findAPositionAndSnap();
      }, time);
    };
  }, [enableScroll, findAPositionAndSnap]);
  const onInput = useCallback(e => {
    enableScroll();
    onScrollEnd(66)();
  }, [enableScroll, onScrollEnd]);
  const onInputStart = useCallback(() => {
    var _animation$current2;
    scrollStart.current = getScrollPosition();
    (_animation$current2 = animation.current) === null || _animation$current2 === void 0 ? void 0 : _animation$current2.stop();
    enableScroll();
    isInteracting.current = true;
  }, [enableScroll]);
  const onInputEnd = useCallback(() => {
    isInteracting.current = false;
    findAPositionAndSnap();
    scrollStart.current = null;
  }, [findAPositionAndSnap]);
  const onTouchStart = useCallback(e => {
    const touch = e.changedTouches[0];
    swipe.current = {};
    swipe.current.xStart = touch.clientX;
    swipe.current.yStart = touch.clientY;
    swipe.current.startTime = window.performance ? window.performance.now() : Date.now();
    onInputStart();
  }, [onInputStart]);
  const onTouchEnd = useCallback(e => {
    if (!swipe.current) return;
    const touch = e.changedTouches[0];
    const endTime = window.performance ? window.performance.now() : Date.now();
    const travelTime = endTime - swipe.current.startTime;
    swipe.current.xSpeed = Math.abs(swipe.current.xStart - touch.clientX) / travelTime;
    swipe.current.ySpeed = Math.abs(swipe.current.yStart - touch.clientY) / travelTime;
    const container = scrollContainerRef.current;
    container.style.overflow = 'hidden';
    onInputEnd();
    swipe.current = null;
  }, [onInputEnd]);
  const passiveSupported = useMemo(() => {
    let supported = false;
    try {
      const options = {
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
  useEventListener('resize', () => setWindowSize({
    height: window.innerHeight,
    width: window.innerWidth
  }), window);
  const snapTo = useCallback((index, disableAnimation = false) => {
    if (disableAnimation) {
      const {
        top,
        left
      } = snapPositionList.current[index] || snapPositionList.current[0];
      scrollContainerRef.current.scrollTo({
        top,
        left
      });
      return;
    }
    snapToDestination(snapPositionList.current[index]);
  }, [snapToDestination, snapPositionList]);
  return {
    snapTo,
    isInteracting,
    windowSize
  };
}
function useScrollIntoView(containerRef, duration = 250, easing = 'ease-out') {
  const animation = useRef(new Animation({
    duration,
    easing
  }));
  const getScrollPosition = useCallback(() => {
    const container = containerRef.current;
    return {
      top: container.scrollTop,
      left: container.scrollLeft
    };
  }, [containerRef]);
  const getBoundryBox = useCallback(() => {
    const container = containerRef.current;
    const scroll = getScrollPosition();
    return {
      ...scroll,
      bottom: scroll.top + container.clientHeight,
      right: scroll.left + container.clientWidth,
      scrollWidth: container.scrollWidth - container.clientWidth,
      scrollHeight: container.scrollHeight - container.clientHeight
    };
  }, [getScrollPosition, containerRef]);
  const getRelativeBoundryBox = useCallback(element => {
    return {
      left: element.offsetLeft,
      top: element.offsetTop,
      right: element.offsetLeft + element.offsetWidth,
      bottom: element.offsetTop + element.offsetHeight
    };
  }, []);
  const containsChild = useCallback(child => {
    const container = containerRef.current;
    if (window.document.contains) {
      return container.contains(child);
    }
    let node = child.parentNode;
    while (node != null) {
      if (node === container) {
        return true;
      }
      node = node.parentNode;
    }
    return false;
  }, [containerRef]);
  const scrollToDestination = useCallback(destination => {
    const container = containerRef.current;
    const scroll = getScrollPosition();
    const distX = destination.left - scroll.left;
    const distY = destination.top - scroll.top;
    const draw = progress => {
      container.scrollLeft = scroll.left + distX * progress;
      container.scrollTop = scroll.top + distY * progress;
    };
    animation.current.stop();
    animation.current.update(draw);
    animation.current.start();
  }, [getScrollPosition, containerRef]);
  return useCallback((element, offset) => {
    if (!containsChild(element)) return;
    const OFFSET = {};
    OFFSET.x = typeof offset === 'object' ? Number(offset.x) || 0 : Number(offset) || 0;
    OFFSET.y = typeof offset === 'object' ? Number(offset.y) || 0 : Number(offset) || 0;
    const boundry = getBoundryBox();
    const childRect = getRelativeBoundryBox(element);
    const deltaX = childRect.left - OFFSET.x > boundry.left && childRect.right + OFFSET.x > boundry.right ? childRect.right - boundry.right + OFFSET.x : childRect.left - OFFSET.x < boundry.left && childRect.right + OFFSET.x < boundry.right ? childRect.left - boundry.left - OFFSET.x : 0;
    const deltaY = childRect.top > boundry.top && childRect.bottom > boundry.bottom ? childRect.bottom - boundry.bottom + OFFSET.y : childRect.top < boundry.top && childRect.bottom < boundry.bottom ? childRect.top - boundry.top - OFFSET.y : 0;
    const top = Math.max(0, Math.min(boundry.top + deltaY, boundry.scrollHeight));
    const left = Math.max(0, Math.min(boundry.left + deltaX, boundry.scrollWidth));
    const destination = {
      top,
      left
    };
    scrollToDestination(destination);
  }, [containsChild, getBoundryBox, getRelativeBoundryBox, scrollToDestination]);
}
function useEventListener(eventName, handler, element, options) {
  const _handler = useRef();
  useEffect(() => {
    _handler.current = handler;
  }, [handler]);
  useEffect(() => {
    const isHTMLElement = element && element.addEventListener;
    if (!isHTMLElement) return;
    const eventHandler = e => _handler.current(e);
    element.addEventListener(eventName, eventHandler, options);
    return () => element.removeEventListener(eventName, eventHandler, options);
  }, [eventName, element]);
}

const TabProvider = React.createContext();
const LAYOUT_PROP_NAMES = {
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
const LAYOUT_PROP_VALUES = {
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
function ScrollSnapTabs({
  children,
  defaultKey,
  eventKeys,
  style,
  className,
  layout,
  snapDuration,
  snapThreshold,
  swipeThreshold,
  easing,
  indicatorClass,
  indicatorColor,
  indicatorStyle,
  indicatorSize,
  onIndicatorMove,
  activeLinkClass,
  activeLinkStyle,
  indicatorParentStyle,
  indicatorParentClass,
  scrollIntoViewDuration,
  scrollIntoViewEasing,
  scrollIntoViewOffset,
  linkStyle,
  linkClass,
  ...rest
}) {
  const propValues = layout === 'horizontal' ? LAYOUT_PROP_VALUES.horizontal : LAYOUT_PROP_VALUES.vertical;
  const propNames = layout === 'horizontal' ? LAYOUT_PROP_NAMES.horizontal : LAYOUT_PROP_NAMES.vertical;
  const [currentEvent, setCurrentEvent] = useState(null);
  const [events, setEvents] = useState([]);
  const indicatorRef = useRef(null);
  const onIndicatorMoveRef = useRef(onIndicatorMove);
  const contentRef = useRef(null);
  const snapTo = useRef(null);
  const linkMapRef = useRef(new Map());
  useEffect(() => {
    if (!currentEvent && events.length > 0) {
      setCurrentEvent(defaultKey || events[0]);
    }
  }, [events, setCurrentEvent]);
  return /*#__PURE__*/React.createElement(TabProvider.Provider, {
    value: {
      eventHandler: [currentEvent, setCurrentEvent],
      events: [events, setEvents],
      indicatorRef,
      contentRef,
      linkMapRef,
      onIndicatorMoveRef,
      snapTo,
      propValues,
      propNames,
      defaultKey: defaultKey || events[0],
      navOptions: {
        indicatorClass,
        indicatorStyle,
        indicatorColor,
        activeLinkClass,
        activeLinkStyle,
        indicatorParentStyle,
        indicatorParentClass,
        indicatorSize,
        scrollIntoViewDuration,
        scrollIntoViewEasing,
        scrollIntoViewOffset,
        linkStyle,
        linkClass
      },
      options: {
        duration: snapDuration,
        easing,
        threshold: snapThreshold,
        swipeThreshold
      }
    }
  }, /*#__PURE__*/React.createElement("div", Object.assign({
    className: [styles.tabs, className].join(' ').trim(),
    style: {
      display: 'flex',
      flexDirection: propValues.wrapperflexDirection,
      height: '100%',
      width: '100%',
      ...style
    }
  }, rest), eventKeys && /*#__PURE__*/React.createElement(Nav, {
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
function Nav({
  eventKeys,
  className,
  activeLinkClass,
  activeLinkStyle,
  indicatorColor,
  indicatorClass,
  indicatorSize,
  indicatorStyle,
  onIndicatorMove,
  indicatorParentStyle,
  indicatorParentClass,
  scrollIntoViewDuration,
  scrollIntoViewEasing,
  scrollIntoViewOffset,
  children,
  style,
  linkStyle,
  linkClass,
  __TYPE,
  ...rest
}) {
  const {
    indicatorRef,
    propValues,
    propNames,
    navOptions,
    linkMapRef,
    eventHandler,
    onIndicatorMoveRef,
    layout
  } = useContext(TabProvider);
  const navContainerRef = useRef();
  const [currentEvent] = eventHandler;
  const scrollIntoRelativeView = useScrollIntoView(navContainerRef, scrollIntoViewDuration || navOptions.scrollIntoViewDuration, scrollIntoViewEasing || navOptions.scrollIntoViewEasing);
  const createNavLinks = (event, i) => {
    return /*#__PURE__*/React.createElement(Link, {
      key: i,
      eventKey: event,
      style: {
        ...navOptions.linkStyle,
        ...linkStyle
      },
      className: linkClass || navOptions.linkClass,
      activeStyle: {
        color: '#5A90E4',
        ...navOptions.activeLinkStyle,
        ...activeLinkStyle
      },
      activeClass: activeLinkClass || navOptions.activeLinkClass
    });
  };
  useLayoutEffect(() => {
    if (typeof onIndicatorMove === 'function') onIndicatorMoveRef.current = onIndicatorMove;
  }, []);
  useEffect(() => {
    scrollIntoRelativeView(linkMapRef.current.get(currentEvent), scrollIntoViewOffset || navOptions.scrollIntoViewOffset || 100);
  }, [currentEvent, scrollIntoRelativeView, scrollIntoViewOffset]);
  const _children = useMemo(() => {
    return children && React.Children.map(children, child => {
      if (React.isValidElement(child) && child.props.__TYPE === 'Link') {
        return React.cloneElement(child, {
          style: {
            ...linkStyle,
            ...navOptions.linkStyle,
            ...child.props.style
          },
          className: [child.props.className, linkClass, navOptions.linkClass].join(' ').trim(),
          activeClass: child.props.activeClass || activeLinkClass || navOptions.activeLinkClass,
          activeStyle: {
            ...navOptions.activeLinkStyle,
            ...activeLinkStyle,
            ...child.props.activeStyle
          }
        });
      }
      return child;
    });
  }, [children, activeLinkClass]);
  const defaultStyle = {
    display: 'flex',
    flexDirection: propValues.flexDirection,
    flex: '0 0 auto',
    position: 'relative',
    overflow: 'auto',
    scrollbarWidth: 'none'
  };
  return /*#__PURE__*/React.createElement("div", Object.assign({
    ref: navContainerRef,
    style: {
      ...style,
      ...defaultStyle
    },
    className: [styles['tab-nav'], className].join(' ').trim()
  }, rest), _children || eventKeys && eventKeys.map(createNavLinks), /*#__PURE__*/React.createElement("div", {
    style: {
      position: 'absolute',
      bottom: propValues.indicatorBottom,
      right: propValues.indicatorRight,
      ...navOptions.indicatorParentStyle,
      ...indicatorParentStyle
    },
    className: indicatorParentClass || navOptions.indicatorParentClass,
    ref: indicatorRef
  }, /*#__PURE__*/React.createElement("div", {
    className: indicatorClass || navOptions.indicatorClass || '',
    style: {
      width: layout === 'horizontal' ? '100%' : indicatorSize || navOptions.indicatorSize,
      height: layout === 'horizontal' ? indicatorSize || navOptions.indicatorSize : '100%',
      margin: 'auto ',
      [propNames.minHeight]: '3px',
      backgroundColor: indicatorColor || navOptions.indicatorColor || 'black',
      ...navOptions.indicatorStyle,
      ...indicatorStyle
    }
  })));
}
Nav.propTypes = {
  eventKeys: propTypes.arrayOf(propTypes.string),
  activeLinkClass: propTypes.string,
  activeLinkStyle: propTypes.object,
  indicatorColor: propTypes.string,
  indicatorClass: propTypes.string,
  indicatorSize: propTypes.string,
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
function Link({
  eventKey,
  className,
  children,
  style,
  activeStyle,
  activeClass,
  __TYPE,
  ...rest
}) {
  const {
    eventHandler,
    events,
    linkMapRef
  } = useContext(TabProvider);
  const [selectedTab, setSelectedTab] = eventHandler;
  const [, setLinks] = events;
  const linkRef = useRef(null);
  const handleClick = e => {
    setSelectedTab(eventKey);
  };
  useLayoutEffect(() => {
    setLinks(prev => [...prev, eventKey]);
    linkMapRef.current.set(eventKey, linkRef.current);
  }, [eventKey, setLinks]);
  const _className = selectedTab === eventKey ? [className, activeClass].join(' ').trim() : className;
  const defaultStyle = {
    cursor: 'pointer',
    padding: '0.5rem',
    ...style
  };
  return /*#__PURE__*/React.createElement("div", Object.assign({
    onClick: handleClick,
    className: _className,
    style: selectedTab === eventKey ? {
      ...defaultStyle,
      ...activeStyle
    } : defaultStyle,
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
function Content({
  children,
  style,
  paneStyle,
  paneClass,
  className,
  ...rest
}) {
  const {
    eventHandler,
    indicatorRef,
    options,
    events,
    linkMapRef,
    contentRef,
    snapTo: _snapTo,
    propValues,
    propNames,
    defaultKey,
    onIndicatorMoveRef
  } = useContext(TabProvider);
  const [links] = events;
  const [currentEvent, setCurrentEvent] = eventHandler;
  const prevScroll = useRef(null);
  const prevEventIndex = useRef(events.indexOf(currentEvent));
  const onSnapStart = useCallback(index => {
    if (currentEvent === links[index]) return;
    setCurrentEvent(links[index]);
  }, [links, setCurrentEvent]);
  const onSnap = useCallback(() => {
    prevEventIndex.current = links.indexOf(currentEvent);
  }, [currentEvent]);
  const {
    snapTo,
    isInteracting,
    windowSize
  } = useScrollSnap({
    ...options,
    scrollContainerRef: contentRef,
    onSnapStart,
    onSnap
  });
  useLayoutEffect(() => {
    _snapTo.current = snapTo;
  }, [snapTo]);
  useEffect(() => {
    if (prevEventIndex.current >= 0) return;
    prevEventIndex.current = links.indexOf(currentEvent);
  }, [currentEvent]);
  const mapNumber = (number, numberMin, numberMax, mapFrom, mapTo) => {
    number = Math.min(numberMax, Math.max(number, numberMin));
    return mapFrom + (number - numberMin) / (numberMax - numberMin) * (mapTo - mapFrom);
  };
  const moveIndicator = (progress, prevIndex, direction, scrollValue) => {
    const current = linkMapRef.current.get(links[prevIndex]);
    const currentLeft = current && current[propNames.offsetLeft] || 0;
    const currentWidth = current && current[propNames.offsetWidth] || 0;
    const target = linkMapRef.current.get(links[direction]);
    const targetLeft = target && target[propNames.offsetLeft];
    const targetWidth = target && target[propNames.offsetWidth];
    const indicator = indicatorRef.current;
    if (!indicator) return;
    indicator.style[propNames.left] = mapNumber(progress, 0, 1, currentLeft, targetLeft) + 'px';
    indicator.style[propNames.width] = mapNumber(progress, 0, 1, currentWidth, targetWidth) + 'px';
    if (typeof onIndicatorMoveRef.current === 'function') {
      const activeIndex = links.indexOf(currentEvent);
      if (isInteracting.current) {
        prevEventIndex.current = activeIndex;
      }
      const movementDir = direction - prevIndex;
      if (movementDir < 0 && prevEventIndex.current < activeIndex || movementDir > 0 && prevEventIndex.current > activeIndex) {
        prevEventIndex.current = prevIndex;
      }
      let _targetIndex = isInteracting.current ? direction : activeIndex;
      let _prevIndex = isInteracting.current ? prevIndex : prevEventIndex.current;
      if (_prevIndex === activeIndex) {
        _prevIndex = direction === activeIndex ? prevIndex : direction;
        _targetIndex = direction === activeIndex ? direction : prevIndex;
      }
      const delta = _targetIndex - _prevIndex;
      let _progress = delta === 0 ? 1 : Math.abs((scrollValue - _prevIndex) / delta);
      _progress = Math.min(1, Math.max(_progress, 0));
      _progress = _progress > 0.995 ? 1 : _progress;
      onIndicatorMoveRef.current({
        target: indicatorRef.current.firstChild,
        progress: _progress,
        isInteracting: isInteracting.current
      });
    }
  };
  const handleScroll = e => {
    if (e.target !== contentRef.current) return;
    let prevIndex, direction;
    const container = e.target;
    let scrollValue = Number(container.scrollLeft / container.clientWidth) || Number(container.scrollTop / container.clientHeight);
    scrollValue = Number(scrollValue.toFixed(2));
    if (prevScroll.current - scrollValue > 0) {
      prevIndex = Math.ceil(scrollValue);
      direction = Math.floor(scrollValue);
    } else {
      direction = Math.ceil(scrollValue);
      prevIndex = Math.floor(scrollValue);
    }
    let unitScroll = Math.abs(prevIndex - scrollValue);
    if (unitScroll > 1) {
      unitScroll = 1;
      prevIndex = direction;
    }
    prevScroll.current = scrollValue;
    moveIndicator(unitScroll, prevIndex, direction, scrollValue);
  };
  useLayoutEffect(() => {
    const currIndex = links.indexOf(defaultKey);
    snapTo(currIndex, true);
    moveIndicator(1, currIndex, currIndex);
  }, [links, indicatorRef]);
  useLayoutEffect(() => {
    const index = links.indexOf(currentEvent);
    moveIndicator(1, index, index);
  }, [windowSize]);
  const _children = useMemo(() => {
    return children && React.Children.map(children, child => {
      if (React.isValidElement(child) && child.props.__TYPE === 'Pane') {
        return React.cloneElement(child, {
          style: {
            ...paneStyle,
            ...child.props.style
          },
          className: [child.props.className, paneClass].join(' ').trim()
        });
      }
      return child;
    });
  }, [children, paneClass]);
  const defaultStyle = {
    position: 'relative',
    display: 'flex',
    flexDirection: propValues.flexDirection,
    flexGrow: '1',
    overflow: 'auto'
  };
  return /*#__PURE__*/React.createElement("div", Object.assign({
    className: [styles['tab-content'], className].join(' ').trim(),
    ref: contentRef,
    onScroll: handleScroll,
    style: {
      ...defaultStyle,
      ...style
    }
  }, rest), _children);
}
Content.propTypes = {
  paneClass: propTypes.string,
  paneStyle: propTypes.object
};
function Pane({
  children,
  eventKey,
  __TYPE,
  style,
  ...rest
}) {
  const paneRef = useRef(null);
  const {
    eventHandler,
    events,
    snapTo
  } = useContext(TabProvider);
  const [currentEvent] = eventHandler;
  const [links] = events;
  useEffect(() => {
    if (links.length > 0 && eventKey === currentEvent) snapTo.current(links.indexOf(eventKey));
  });
  return /*#__PURE__*/React.createElement("div", Object.assign({
    ref: paneRef,
    style: {
      overflow: 'auto',
      ...style
    }
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

export default ScrollSnapTabs;
//# sourceMappingURL=index.modern.js.map
