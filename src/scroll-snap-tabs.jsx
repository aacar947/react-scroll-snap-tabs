/* eslint-disable prettier/prettier */
import React, { useState, useContext, useRef, useEffect, useLayoutEffect, useCallback, useMemo } from 'react'
import PropTypes from 'prop-types'
import styles from './styles.module.css'
import { useScrollSnap, useScrollIntoView } from './utilities'
const TabProvider = React.createContext()

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
}

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
}

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
  const propValues = layout === 'horizontal' ? LAYOUT_PROP_VALUES.horizontal : LAYOUT_PROP_VALUES.vertical
  const propNames = layout === 'horizontal' ? LAYOUT_PROP_NAMES.horizontal : LAYOUT_PROP_NAMES.vertical

  const [currentEvent, setCurrentEvent] = useState(null)
  const [events, setEvents] = useState([])
  const indicatorRef = useRef(null)
  const onIndicatorMoveRef = useRef(onIndicatorMove)
  const contentRef = useRef(null)
  const snapTo = useRef(null)
  const linkMapRef = useRef(new Map())

  useEffect(() => {
    if (!currentEvent && events.length > 0) {
      setCurrentEvent(defaultKey || events[0])
    }
  }, [events, setCurrentEvent])

  return (
    <TabProvider.Provider
      value={{
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
      }}
    >
      <div
        className={[styles.tabs, className].join(' ').trim()}
        style={{
          display: 'flex',
          flexDirection: propValues.wrapperflexDirection,
          height: '100%',
          width: '100%',
          ...style
        }}
        {...rest}
      >
        {eventKeys && <Nav eventKeys={eventKeys} />}
        {children}
      </div>
    </TabProvider.Provider>
  )
}

ScrollSnapTabs.propTypes = {
  defaultKey: PropTypes.string,
  eventKeys: PropTypes.arrayOf(PropTypes.string),
  layout: PropTypes.string,
  snapDuration: PropTypes.number,
  easing: PropTypes.oneOfType([PropTypes.func, PropTypes.string]),
  indicatorClass: PropTypes.string,
  indicatorParentClass: PropTypes.string,
  indicatorStyle: PropTypes.object,
  indicatorParentStyle: PropTypes.object,
  indicatorSize: PropTypes.string,
  onIndicatorMove: PropTypes.func,
  activeLinkClass: PropTypes.string,
  activeLinkStyle: PropTypes.object,
  scrollIntoViewDuration: PropTypes.number,
  scrollIntoViewEasing: PropTypes.oneOfType([PropTypes.string, PropTypes.func]),
  scrollIntoViewOffset: PropTypes.number
}

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
  } = useContext(TabProvider)
  const navContainerRef = useRef()
  const [currentEvent] = eventHandler
  const scrollIntoRelativeView = useScrollIntoView(
    navContainerRef,
    scrollIntoViewDuration || navOptions.scrollIntoViewDuration,
    scrollIntoViewEasing || navOptions.scrollIntoViewEasing
  )
  const createNavLinks = (event, i) => {
    return (
      <Link
        key={i}
        eventKey={event}
        style={{ ...navOptions.linkStyle, ...linkStyle }}
        className={linkClass || navOptions.linkClass}
        activeStyle={{ color: '#5A90E4', ...navOptions.activeLinkStyle, ...activeLinkStyle }}
        activeClass={activeLinkClass || navOptions.activeLinkClass}
      />
    )
  }

  useLayoutEffect(() => {
    if (typeof onIndicatorMove === 'function') onIndicatorMoveRef.current = onIndicatorMove
  }, [])

  useEffect(() => {
    scrollIntoRelativeView(
      linkMapRef.current.get(currentEvent),
      scrollIntoViewOffset || navOptions.scrollIntoViewOffset || 100
    )
  }, [currentEvent, scrollIntoRelativeView, scrollIntoViewOffset])
  const _children = useMemo(() => {
    return (
      children &&
      React.Children.map(children, (child) => {
        if (React.isValidElement(child) && child.props.__TYPE === 'Link') {
          return React.cloneElement(child, {
            style: { ...linkStyle, ...navOptions.linkStyle, ...child.props.style },
            className: [child.props.className, linkClass, navOptions.linkClass].join(' ').trim(),
            activeClass: child.props.activeClass || activeLinkClass || navOptions.activeLinkClass,
            activeStyle: {
              ...navOptions.activeLinkStyle,
              ...activeLinkStyle,
              ...child.props.activeStyle
            }
          })
        }
        return child
      })
    )
  }, [children, activeLinkClass])
  const defaultStyle = {
    display: 'flex',
    flexDirection: propValues.flexDirection,
    position: 'relative',
    overflow: 'auto',
    scrollbarWidth: 'none'
  }

  return (
    <div
      ref={navContainerRef}
      style={{ ...style, ...defaultStyle }}
      className={[styles['tab-nav'], className].join(' ').trim()}
      {...rest}
    >
      {_children || (eventKeys && eventKeys.map(createNavLinks))}
      <div
        style={{
          position: 'absolute',
          bottom: propValues.indicatorBottom,
          right: propValues.indicatorRight,
          ...navOptions.indicatorParentStyle,
          ...indicatorParentStyle
        }}
        className={indicatorParentClass || navOptions.indicatorParentClass}
        ref={indicatorRef}
      >
        <div
          className={indicatorClass || navOptions.indicatorClass || ''}
          style={{
            width: layout === 'horizontal' ? '100%' : indicatorSize || navOptions.indicatorSize,
            height: layout === 'horizontal' ? indicatorSize || navOptions.indicatorSize : '100%',
            margin: 'auto ',
            [propNames.minHeight]: '3px',
            backgroundColor: indicatorColor || navOptions.indicatorColor || 'black',
            ...navOptions.indicatorStyle,
            ...indicatorStyle
          }}
        />
      </div>
    </div>
  )
}
Nav.propTypes = {
  eventKeys: PropTypes.arrayOf(PropTypes.string),
  activeLinkClass: PropTypes.string,
  activeLinkStyle: PropTypes.object,
  indicatorColor: PropTypes.string,
  indicatorClass: PropTypes.string,
  indicatorSize: PropTypes.number,
  indicatorStyle: PropTypes.object,
  onIndicatorMove: PropTypes.func,
  linkStyle: PropTypes.object,
  linkClass: PropTypes.string,
  scrollIntoViewDuration: PropTypes.number,
  scrollIntoViewEasing: PropTypes.oneOfType([PropTypes.string, PropTypes.func]),
  scrollIntoViewOffset: PropTypes.number,
  __TYPE: PropTypes.string
}

Nav.defaultProps = {
  __TYPE: 'Nav'
}

function Link({ eventKey, className, children, style, activeStyle, activeClass, __TYPE, ...rest }) {
  const { eventHandler, events, linkMapRef } = useContext(TabProvider)
  const [selectedTab, setSelectedTab] = eventHandler
  const [, setLinks] = events
  const linkRef = useRef(null)

  const handleClick = (e) => {
    setSelectedTab(eventKey)
  }

  useLayoutEffect(() => {
    setLinks((prev) => [...prev, eventKey])
    linkMapRef.current.set(eventKey, linkRef.current)
  }, [eventKey, setLinks])

  const _className = selectedTab === eventKey ? [className, activeClass].join(' ').trim() : className
  const defaultStyle = { cursor: 'pointer', padding: '0.5rem', ...style }
  return (
    <div
      onClick={handleClick}
      className={_className}
      style={selectedTab === eventKey ? { ...defaultStyle, ...activeStyle } : defaultStyle}
      ref={linkRef}
      {...rest}
    >
      {children || eventKey}
    </div>
  )
}

Link.propTypes = {
  eventKey: PropTypes.string,
  activeStyle: PropTypes.object,
  activeClass: PropTypes.string,
  __TYPE: PropTypes.string
}

Link.defaultProps = {
  __TYPE: 'Link'
}

function Content({ children, style, paneStyle, paneClass, className, ...rest }) {
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
  } = useContext(TabProvider)

  const [links] = events
  const [currentEvent, setCurrentEvent] = eventHandler
  const prevScroll = useRef(null)
  const prevEventIndex = useRef(events.indexOf(currentEvent))

  const onSnapStart = useCallback(
    (index) => {
      if (currentEvent === links[index]) return
      setCurrentEvent(links[index])
    },
    [links, setCurrentEvent]
  )

  const onSnap = useCallback(() => {
    prevEventIndex.current = links.indexOf(currentEvent)
  }, [currentEvent])

  const { snapTo, isInteracting } = useScrollSnap({
    ...options,
    scrollContainerRef: contentRef,
    onSnapStart,
    onSnap
  })

  useLayoutEffect(() => {
    _snapTo.current = snapTo
  }, [snapTo])

  useEffect(() => {
    if (prevEventIndex.current >= 0) return
    prevEventIndex.current = links.indexOf(currentEvent)
  }, [currentEvent])

  const mapNumber = (number, numberMin, numberMax, mapFrom, mapTo) => {
    number = Math.min(numberMax, Math.max(number, numberMin))
    return mapFrom + ((number - numberMin) / (numberMax - numberMin)) * (mapTo - mapFrom)
  }

  const moveIndicator = (progress, prevIndex, direction, scrollValue) => {
    const current = linkMapRef.current.get(links[prevIndex])
    const currentLeft = (current && current[propNames.offsetLeft]) || 0
    const currentWidth = (current && current[propNames.offsetWidth]) || 0
    const target = linkMapRef.current.get(links[direction])
    const targetLeft = target && target[propNames.offsetLeft]
    const targetWidth = target && target[propNames.offsetWidth]
    const indicator = indicatorRef.current

    if (!indicator) return
    indicator.style[propNames.left] = mapNumber(progress, 0, 1, currentLeft, targetLeft) + 'px'
    indicator.style[propNames.width] = mapNumber(progress, 0, 1, currentWidth, targetWidth) + 'px'

    if (typeof onIndicatorMoveRef.current === 'function') {
      const activeIndex = links.indexOf(currentEvent)
      if (isInteracting.current) {
        prevEventIndex.current = activeIndex
      }

      const movementDir = direction - prevIndex
      if (
        (movementDir < 0 && prevEventIndex.current < activeIndex) ||
        (movementDir > 0 && prevEventIndex.current > activeIndex)
      ) {
        prevEventIndex.current = prevIndex
      }

      let _targetIndex = isInteracting.current ? direction : activeIndex
      let _prevIndex = isInteracting.current ? prevIndex : prevEventIndex.current

      if (_prevIndex === activeIndex) {
        _prevIndex = direction === activeIndex ? prevIndex : direction
        _targetIndex = direction === activeIndex ? direction : prevIndex
      }

      const delta = _targetIndex - _prevIndex
      let _progress = delta === 0 ? 1 : Math.abs((scrollValue - _prevIndex) / delta)
      _progress = Math.min(1, Math.max(_progress, 0))
      onIndicatorMoveRef.current({
        target: indicatorRef.current.firstChild,
        progress: _progress,
        isInteracting: isInteracting.current
      })
    }
  }

  const handleScroll = (e) => {
    let prevIndex, direction
    const scrollValue =
      Number(e.target.scrollLeft / e.target.clientWidth) || Number(e.target.scrollTop / e.target.clientHeight)
    if (prevScroll.current - scrollValue > 0) {
      prevIndex = Math.ceil(scrollValue)
      direction = Math.floor(scrollValue)
    } else {
      direction = Math.ceil(scrollValue)
      prevIndex = Math.floor(scrollValue)
    }

    let unitScroll = Math.abs(prevIndex - scrollValue)
    if (unitScroll > 1) {
      unitScroll = 1
      prevIndex = direction
    }

    prevScroll.current = scrollValue
    moveIndicator(unitScroll, prevIndex, direction, scrollValue)
  }

  useLayoutEffect(() => {
    const currIndex = links.indexOf(defaultKey)
    snapTo(currIndex, true)
    moveIndicator(1, currIndex, currIndex)
  }, [links, indicatorRef])

  const _children = useMemo(() => {
    return (
      children &&
      React.Children.map(children, (child) => {
        if (React.isValidElement(child) && child.props.__TYPE === 'Pane') {
          return React.cloneElement(child, {
            style: { ...paneStyle, ...child.props.style },
            className: [child.props.className, paneClass].join(' ').trim()
          })
        }
        return child
      })
    )
  }, [children, paneClass])

  const defaultStyle = {
    position: 'relative',
    display: 'flex',
    flexDirection: propValues.flexDirection,
    flexGrow: '1',
    overflow: 'auto'
  }

  return (
    <div
      className={[styles['tab-content'], className].join(' ').trim()}
      ref={contentRef}
      onScroll={handleScroll}
      style={{ ...defaultStyle, ...style }}
      {...rest}
    >
      {_children}
    </div>
  )
}

Content.propTypes = {
  paneClass: PropTypes.string,
  paneStyle: PropTypes.object
}

function Pane({ children, eventKey, __TYPE, ...rest }) {
  const paneRef = useRef(null)
  const { eventHandler, events, snapTo } = useContext(TabProvider)
  const [currentEvent] = eventHandler
  const [links] = events

  useEffect(() => {
    if (links.length > 0 && eventKey === currentEvent) snapTo.current(links.indexOf(eventKey))
  })

  return (
    <div ref={paneRef} {...rest}>
      {children}
    </div>
  )
}

Pane.propTypes = {
  eventKey: PropTypes.string,
  __TYPE: PropTypes.string
}

Pane.defaultProps = {
  __TYPE: 'Pane'
}

ScrollSnapTabs.Nav = Nav
ScrollSnapTabs.Link = Link
ScrollSnapTabs.Content = Content
ScrollSnapTabs.Pane = Pane
export default ScrollSnapTabs
