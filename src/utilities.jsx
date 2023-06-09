/* eslint-disable dot-notation */
/* eslint-disable no-unused-expressions */
/* eslint-disable prettier/prettier */
import { useState, useRef, useEffect, useCallback, useLayoutEffect, useMemo } from 'react'

const defaultOptions = {
  duration: 300,
  easing: 'ease-out',
  fireAnimationEndEventOnStop: false
}
class Animation {
  progress
  requestId
  constructor(options) {
    const _options = { ...defaultOptions, ...options }
    switch (_options.easing) {
      case 'ease-in':
        _options.timing = (t) => t * t
        break
      case 'ease-out':
        _options.timing = (t) => 1 - Math.pow(1 - t, 2)
        break
      case 'ease-in-out':
        _options.timing = (t) => (t < 0.5 ? 2 * t * t : 1 - Math.pow(2 - 2 * t, 2) / 2)
        break
      default:
        if (typeof _options.easing === 'function') {
          _options.timing = _options.easing
          break
        }
        _options.timing = (t) => t
        break
    }
    this.options = _options
    this.stopped = true
    this.started = false
    this._events = {}
  }

  start() {
    const timing = this.options.timing
    const update = this.options.update
    const duration = this.options.duration
    if (!window.requestAnimationFrame) {
      update(1)
      if (this._events['end']) {
        this._emit('end', this.progress)
      }
      console.warn('Your browser does not support window.requestAnimationFrame')
      return
    }
    let startTime = window.performance.now()
    function _animate(time) {
      if (!this.started) {
        if (this._events['start']) this._emit('start')
        this.started = true
      }
      if (this.stopped) {
        if (this._events['end'] && this.options.fireAnimationEndEventOnStop) this.emit('end', this.progress)
        return
      }
      // timeFraction goes from 0 to 1
      let timeFraction = (time - startTime) / duration
      if (timeFraction < 0) {
        timeFraction = 0
        startTime = time
      }
      if (timeFraction > 1) {
        timeFraction = 1
        this.stopped = true
        if (this._events['end']) {
          this._emit('end', this.progress)
        }
      }
      // calculate the current animation state
      const progress = timing(timeFraction)
      // update it
      this.progress = progress
      if (this.options.fromTo) {
        const fromTo = this.options.fromTo
        const dist = fromTo[1] - fromTo[0]
        update(fromTo[0] + progress * dist)
      } else {
        update(progress)
      }
      if (timeFraction < 1) {
        this.requestId = window.requestAnimationFrame(_animate.bind(this))
      }
    }
    this.requestId = window.requestAnimationFrame(_animate.bind(this))
  }

  stop() {
    window.cancelAnimationFrame(this.requestId)
    this.stopped = true
  }

  update(callback) {
    this.options.update = callback
    this.stopped = false
    this.started = false
    return this
  }

  on(name, callback) {
    if (!this._events[name]) {
      this._events[name] = []
    }
    this._events[name].push(callback)
  }

  removeListener(name, callback) {
    if (!this._events[name]) return
    const filterListeners = (listener) => listener !== callback
    this._events[name] = this._events[name].filter(filterListeners)
  }

  removeAllListeners() {
    this._events = {}
  }

  _emit(name, data) {
    if (!this._events[name]) {
      console.warn(`Can't emit an event. Event "${name}" doesn't exits.`)
      return
    }
    this._events[name].forEach((callback) => {
      callback(data)
    })
  }
}

let CONTAINER_INDEX = 0
export function useScrollSnap({
  scrollContainerRef,
  childrenSelector = '> div',
  threshold = 30,
  swipeThreshold = 200,
  easing = 'ease-out',
  duration = 250,
  onSnapStart,
  onSnap
}) {
  const [windowSize, setWindowSize] = useState(null)
  const isInteracting = useRef(false)
  const animation = useRef(null)
  const snapPositionList = useRef([])
  const activePosition = useRef()
  const index = useRef(null)
  const swipe = useRef(null)
  const scrollStart = useRef(null)
  const timeOut = useRef(null)

  useLayoutEffect(() => {
    index.current = CONTAINER_INDEX
    scrollContainerRef.current.dataset.snapContainerId = index.current
    scrollContainerRef.current.style.position = 'relative'
    animation.current = new Animation({ easing, duration })
    CONTAINER_INDEX++
  }, [])

  useLayoutEffect(() => {
    const reduceToSnapPositions = (positions, child, i) => [
      ...positions,
      {
        index: i,
        top: child.offsetTop,
        left: child.offsetLeft,
        right: child.offsetLeft + child.offsetWidth,
        bottom: child.offsetTop + child.offsetHeight
      }
    ]
    const query = `[data-snap-container-id="${index.current}"] ${childrenSelector}`
    snapPositionList.current = Array.from(scrollContainerRef.current.querySelectorAll(query)).reduce(
      reduceToSnapPositions,
      []
    )
    if (!activePosition.current || !scrollContainerRef.current) return
    const container = scrollContainerRef.current
    activePosition.current = snapPositionList.current[activePosition.current.index]
    container.scrollLeft = activePosition.current.left
    container.scrollTop = activePosition.current.top
    console.log('size changed', activePosition.current.left)
  }, [childrenSelector, windowSize])

  useLayoutEffect(() => {
    activePosition.current = snapPositionList.current[0]
  }, [])

  const getScrollPosition = useCallback(() => {
    const container = scrollContainerRef.current
    return {
      top: container.scrollTop,
      left: container.scrollLeft
    }
  }, [])

  const snapToDestination = useCallback(
    (destination, currentPosition) => {
      if (!destination) return
      currentPosition = currentPosition || getScrollPosition()
      const xDist = destination.left - currentPosition.left
      const yDist = destination.top - currentPosition.top
      if (
        xDist === 0 &&
        yDist === 0 &&
        destination.left === activePosition.current.left &&
        destination.top === activePosition.current.top
      ) {
        if (onSnapStart) onSnapStart(destination.index)
        activePosition.current = destination
        return
      }

      const draw = (progress) => {
        const left = currentPosition.left + progress * xDist
        const top = currentPosition.top + progress * yDist
        scrollContainerRef.current.scrollTo({ top, left })
      }
      animation.current?.stop()
      animation.current.update(draw)
      animation.current.removeAllListeners()
      animation.current.on('start', () => {
        if (onSnapStart) onSnapStart(destination.index)
        activePosition.current = destination
      })
      animation.current.on('end', () => {
        clearTimeout(timeOut.current)
        if (onSnap) onSnap(destination.index)
      })
      animation.current.start()
    },
    [getScrollPosition, onSnapStart, onSnap]
  )

  const getPositionsInViewport = useCallback(
    (container) => {
      const scroll = getScrollPosition()
      const boundry = {
        ...scroll,
        right: scroll.left + container.clientWidth,
        bottom: scroll.top + container.clientHeight
      }

      return snapPositionList.current.filter((pos) => {
        return (
          pos.top < boundry.bottom &&
          pos.bottom > boundry.top &&
          pos.left < boundry.right &&
          pos.right > boundry.left
        )
      })
    },
    [getScrollPosition, snapPositionList]
  )

  const getSnapPosition = useCallback(
    (deltaLeft, deltaTop) => {
      const positionsInViewport = getPositionsInViewport(scrollContainerRef.current)

      const index =
        deltaLeft < 0 || deltaTop < 0
          ? positionsInViewport[0].index + 1
          : positionsInViewport[positionsInViewport.length - 1].index - 1
      return snapPositionList.current[index] || positionsInViewport[0]
    },
    [getPositionsInViewport]
  )

  const getNearestPositionInViewport = useCallback(() => {
    const positionsInViewport = getPositionsInViewport(scrollContainerRef.current)
    const scroll = getScrollPosition()
    if (positionsInViewport.length === 1) return positionsInViewport[0]
    return positionsInViewport.sort((a, b) => {
      const leftCenter = (a.left + b.left) / 2
      const topCenter = (a.top + b.top) / 2
      // to fix the reverse sort in firefox (a and b are swapped)
      const reverseFactor = a.left > b.left || a.top > b.top ? 1 : -1
      return (leftCenter - scroll.left) * reverseFactor || (topCenter - scroll.top) * reverseFactor
    })[0]
  }, [getPositionsInViewport, getScrollPosition])

  const isSwipeTresholdExceeded = useCallback(
    (deltaLeft, deltaTop) => {
      if (Math.abs(deltaLeft) <= 5 && Math.abs(deltaTop) <= 5) return false
      const calcWithInertia = () => {
        const DEC = 625 * Math.pow(10, -6)
        const speed =
          swipe.current.xSpeed > swipe.current.ySpeed ? swipe.current.xSpeed : swipe.current.ySpeed
        return (speed * speed) / (2 * DEC) > swipeThreshold
      }

      return Math.abs(deltaTop) > swipeThreshold || Math.abs(deltaLeft) > swipeThreshold || calcWithInertia()
    },
    [swipeThreshold]
  )

  const findAPositionAndSnap = useCallback(() => {
    if (!animation.current.stopped) return

    const scroll = getScrollPosition()
    const deltaLeft = (scrollStart.current?.left || activePosition.current.left) - scroll.left
    const deltaTop = (scrollStart.current?.top || activePosition.current.top) - scroll.top

    let destination
    const tresholdExceeded = swipe.current
      ? isSwipeTresholdExceeded(deltaLeft, deltaTop)
      : Math.abs(deltaLeft) > threshold || Math.abs(deltaTop) > threshold

    if (tresholdExceeded) {
      const snapPosition = getSnapPosition(deltaLeft, deltaTop)
      destination = snapPosition
    } else {
      destination = getNearestPositionInViewport()
    }

    snapToDestination(destination, scroll)
  }, [getScrollPosition, isSwipeTresholdExceeded, threshold, getSnapPosition, snapToDestination])

  const enableScroll = useCallback(() => {
    const container = scrollContainerRef.current
    // to prevent scroll inertia bug on touch devices
    container.style.overflow = 'auto'
  }, [])

  const onScrollEnd = useCallback(
    (time) => {
      return (e) => {
        clearTimeout(timeOut.current)
        if (isInteracting.current || !animation.current.stopped) {
          return
        }
        // Set a timeout to run after scrolling ends
        timeOut.current = setTimeout(() => {
          enableScroll()
          findAPositionAndSnap()
        }, time)
      }
    },
    [enableScroll, findAPositionAndSnap]
  )

  const onInput = useCallback(
    (e) => {
      enableScroll()
      onScrollEnd(66)()
    },
    [enableScroll, onScrollEnd]
  )

  const onInputStart = useCallback(() => {
    scrollStart.current = getScrollPosition()
    animation.current?.stop()
    enableScroll()
    isInteracting.current = true
  }, [enableScroll])

  const onInputEnd = useCallback(() => {
    isInteracting.current = false
    findAPositionAndSnap()
    scrollStart.current = null
  }, [findAPositionAndSnap])

  const onTouchStart = useCallback(
    (e) => {
      const touch = e.changedTouches[0]
      swipe.current = {}
      swipe.current.xStart = touch.clientX
      swipe.current.yStart = touch.clientY
      swipe.current.startTime = window.performance ? window.performance.now() : Date.now()

      onInputStart()
    },
    [onInputStart]
  )

  const onTouchEnd = useCallback(
    (e) => {
      if (!swipe.current) return
      const touch = e.changedTouches[0]
      const endTime = window.performance ? window.performance.now() : Date.now()
      const travelTime = endTime - swipe.current.startTime
      swipe.current.xSpeed = Math.abs(swipe.current.xStart - touch.clientX) / travelTime
      swipe.current.ySpeed = Math.abs(swipe.current.yStart - touch.clientY) / travelTime

      const container = scrollContainerRef.current
      // to prevent scroll inertia bug on touch devices
      container.style.overflow = 'hidden'
      onInputEnd()
      swipe.current = null
    },
    [onInputEnd]
  )

  const passiveSupported = useMemo(() => {
    let supported = false

    try {
      const options = {
        get passive() {
          // This function will be called when the browser
          // attempts to access the passive property.
          supported = true
          return false
        }
      }

      window.addEventListener('test', null, options)
      window.removeEventListener('test', null, options)
    } catch (err) {
      console.warn('window.addEventListener() does not support passive option')
    }
    return supported
  })

  useEventListener(
    'scroll',
    onScrollEnd(44),
    scrollContainerRef.current,
    passiveSupported && { passive: true }
  )
  useEventListener(
    'touchstart',
    onTouchStart,
    scrollContainerRef.current,
    passiveSupported && {
      passive: true
    }
  )
  useEventListener(
    'touchend',
    onTouchEnd,
    scrollContainerRef.current,
    passiveSupported && {
      passive: true
    }
  )
  useEventListener(
    'keydown',
    onInputStart,
    scrollContainerRef.current,
    passiveSupported && {
      passive: true
    }
  )
  useEventListener(
    'keyup',
    onInputEnd,
    scrollContainerRef.current,
    passiveSupported && {
      passive: true
    }
  )
  useEventListener(
    'mousedown',
    onInputStart,
    scrollContainerRef.current,
    passiveSupported && {
      passive: true
    }
  )
  useEventListener(
    'mouseup',
    onInputEnd,
    scrollContainerRef.current,
    passiveSupported && {
      passive: true
    }
  )
  useEventListener(
    'wheel',
    onInput,
    scrollContainerRef.current,
    passiveSupported && {
      passive: true
    }
  )
  useEventListener(
    'resize',
    () =>
      setWindowSize({
        height: window.innerHeight,
        width: window.innerWidth
      }),
    window
  )

  const snapTo = useCallback(
    (index, disableAnimation = false) => {
      if (disableAnimation) {
        const { top, left } = snapPositionList.current[index] || snapPositionList.current[0]
        scrollContainerRef.current.scrollTo({ top, left })
        return
      }
      snapToDestination(snapPositionList.current[index])
    },
    [snapToDestination, snapPositionList]
  )
  return { snapTo, isInteracting, windowSize }
}

export function useScrollIntoView(containerRef, duration = 250, easing = 'ease-out') {
  const animation = useRef(new Animation({ duration, easing }))

  const getScrollPosition = useCallback(() => {
    const container = containerRef.current
    return {
      top: container.scrollTop,
      left: container.scrollLeft
    }
  }, [containerRef])

  const getBoundryBox = useCallback(() => {
    const container = containerRef.current
    const scroll = getScrollPosition()
    return {
      ...scroll,
      bottom: scroll.top + container.clientHeight,
      right: scroll.left + container.clientWidth,
      scrollWidth: container.scrollWidth - container.clientWidth,
      scrollHeight: container.scrollHeight - container.clientHeight
    }
  }, [getScrollPosition, containerRef])

  const getRelativeBoundryBox = useCallback((element) => {
    return {
      left: element.offsetLeft,
      top: element.offsetTop,
      right: element.offsetLeft + element.offsetWidth,
      bottom: element.offsetTop + element.offsetHeight
    }
  }, [])

  const containsChild = useCallback(
    (child) => {
      const container = containerRef.current
      // https://www.geeksforgeeks.org/how-to-check-if-an-element-is-a-child-of-a-parent-using-javascript/
      if (window.document.contains) {
        return container.contains(child)
      }
      let node = child.parentNode
      // keep iterating unless null
      while (node != null) {
        if (node === container) {
          return true
        }
        node = node.parentNode
      }
      return false
    },
    [containerRef]
  )

  const scrollToDestination = useCallback(
    (destination) => {
      const container = containerRef.current

      const scroll = getScrollPosition()
      const distX = destination.left - scroll.left
      const distY = destination.top - scroll.top

      const draw = (progress) => {
        container.scrollLeft = scroll.left + distX * progress
        container.scrollTop = scroll.top + distY * progress
      }

      animation.current.stop()
      animation.current.update(draw)
      animation.current.start()
    },
    [getScrollPosition, containerRef]
  )

  return useCallback(
    (element, offset) => {
      if (!containsChild(element)) return
      const OFFSET = {}
      OFFSET.x = typeof offset === 'object' ? Number(offset.x) || 0 : Number(offset) || 0
      OFFSET.y = typeof offset === 'object' ? Number(offset.y) || 0 : Number(offset) || 0

      const boundry = getBoundryBox()
      const childRect = getRelativeBoundryBox(element)

      const deltaX =
        childRect.left - OFFSET.x > boundry.left && childRect.right + OFFSET.x > boundry.right
          ? childRect.right - boundry.right + OFFSET.x
          : childRect.left - OFFSET.x < boundry.left && childRect.right + OFFSET.x < boundry.right
          ? childRect.left - boundry.left - OFFSET.x
          : 0

      const deltaY =
        childRect.top > boundry.top && childRect.bottom > boundry.bottom
          ? childRect.bottom - boundry.bottom + OFFSET.y
          : childRect.top < boundry.top && childRect.bottom < boundry.bottom
          ? childRect.top - boundry.top - OFFSET.y
          : 0
      const top = Math.max(0, Math.min(boundry.top + deltaY, boundry.scrollHeight))
      const left = Math.max(0, Math.min(boundry.left + deltaX, boundry.scrollWidth))
      const destination = { top, left }
      scrollToDestination(destination)
    },
    [containsChild, getBoundryBox, getRelativeBoundryBox, scrollToDestination]
  )
}

export function useEventListener(eventName, handler, element, options) {
  const _handler = useRef()
  useEffect(() => {
    _handler.current = handler
  }, [handler])
  useEffect(() => {
    const isHTMLElement = element && element.addEventListener
    if (!isHTMLElement) return

    const eventHandler = (e) => _handler.current(e)
    element.addEventListener(eventName, eventHandler, options)

    return () => element.removeEventListener(eventName, eventHandler, options)
  }, [eventName, element])
}
