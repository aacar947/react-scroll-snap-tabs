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
    indicatorLeft: '0'
  }
}

function ScrollSnapTabs({
  children,
  defaultKey,
  eventKeys,
  style,
  layout = 'vertical',
  snapDuration,
  easing,
  indicatorClass,
  indicatorStyle,
  indicatorSize,
  onIndicatorMove
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
        indicatorOptions: {
          indicatorClass,
          indicatorStyle,
          indicatorSize
        },
        options: {
          duration: snapDuration,
          easing
        }
      }}
    >
      <div
        className={styles.tabs}
        style={{
          ...style,
          display: 'flex',
          flexDirection: propValues.wrapperflexDirection,
          height: '100%',
          width: '100%'
        }}
      >
        {eventKeys && <Nav eventKeys={eventKeys} />}
        {children}
      </div>
    </TabProvider.Provider>
  )
}

function Nav({
  eventKeys,
  className,
  activeLinkClass,
  activeLinkStyle = { color: 'green' },
  indicatorColor,
  indicatorClass,
  indicatorSize,
  indicatorStyle,
  onIndicatorMove,
  children,
  style = {},
  linkStyle = {},
  linkClass = ''
}) {
  const {
    indicatorRef,
    propValues,
    propNames,
    indicatorOptions,
    linkMapRef,
    eventHandler,
    onIndicatorMoveRef,
    layout
  } = useContext(TabProvider)
  const navContainerRef = useRef()
  const [currentEvent] = eventHandler
  const scrollIntoRelativeView = useScrollIntoView(navContainerRef)
  const createNavLinks = (event, i) => {
    return (
      <Link
        key={i}
        eventKey={event}
        style={linkStyle}
        className={linkClass}
        activeStyle={activeLinkStyle}
        activeClass={activeLinkClass}
      />
    )
  }

  useLayoutEffect(() => {
    if (typeof onIndicatorMove === 'function') onIndicatorMoveRef.current = onIndicatorMove
  }, [])

  useEffect(() => {
    scrollIntoRelativeView(linkMapRef.current.get(currentEvent), 50)
  }, [currentEvent, scrollIntoRelativeView])
  const _children = useMemo(() => {
    return (
      children &&
      React.Children.map(children, (child) => {
        if (React.isValidElement(child) && child.props.__TYPE === 'Link') {
          return React.cloneElement(child, {
            style: { ...child.props.style, ...linkStyle },
            className: [child.props.className, linkClass].join(' ').trim(),
            activeClass: child.props.activeClass || activeLinkClass,
            activeStyle: child.props.activeStyle || activeLinkStyle
          })
        }
        return child
      })
    )
  }, [children])

  const defaultStyle = {
    display: 'flex',
    flexDirection: propValues.flexDirection,
    position: 'relative',
    overflow: 'auto'
  }

  return (
    <div ref={navContainerRef} style={{ ...style, ...defaultStyle }} className={className}>
      <div
        style={{
          position: 'absolute',
          bottom: propValues.indicatorBottom,
          left: propValues.indicatorLeft
        }}
        ref={indicatorRef}
      >
        <div
          className={indicatorClass || indicatorOptions.indicatorClass || ''}
          style={{
            width: (layout === 'horizontal' && '100%') || indicatorSize || indicatorOptions.indicatorSize,
            height: (layout === 'horizontal' && indicatorSize) || indicatorOptions.indicatorSize || '100%',
            margin: 'auto ',
            [propNames.minHeight]: '3px',
            backgroundColor: indicatorColor || 'black',
            ...indicatorOptions.indicatorStyle,
            ...indicatorStyle
          }}
        />
      </div>
      {_children || (eventKeys && eventKeys.map(createNavLinks))}
    </div>
  )
}
Nav.propTypes = {
  eventKeys: PropTypes.arrayOf(PropTypes.string)
}

function Link({ eventKey, className, children, style, activeStyle, activeClass = 'active' }) {
  const { eventHandler, events, linkMapRef } = useContext(TabProvider)
  const [selectedTab, setSelectedTab] = eventHandler
  const [, setEvents] = events
  const linkRef = useRef(null)

  const handleClick = (e) => {
    setSelectedTab(eventKey)
  }

  useLayoutEffect(() => {
    setEvents((prev) => [...prev, eventKey])
    linkMapRef.current.set(eventKey, linkRef.current)
  }, [eventKey, setEvents])

  const _className = selectedTab === eventKey ? [className, activeClass].join(' ').trim() : className
  const _style = { cursor: 'pointer', margin: '0.5rem', ...style }
  return (
    <div
      onClick={handleClick}
      className={_className}
      style={selectedTab === eventKey ? { ..._style, ...activeStyle } : _style}
      ref={linkRef}
    >
      {children || eventKey}
    </div>
  )
}

Link.propTypes = {
  eventKey: PropTypes.string,
  activeStyle: PropTypes.object,
  __TYPE: PropTypes.string
}

Link.defaultProps = {
  __TYPE: 'Link',
  activeStyle: { textShadow: '0px 0px 1px black' }
}

function Content({ children, style, paneStyle, paneClass, ...rest }) {
  const {
    eventHandler,
    indicatorRef,
    options,
    events,
    linkMapRef,
    contentRef,
    snapTo,
    propValues,
    propNames,
    defaultKey,
    onIndicatorMoveRef
  } = useContext(TabProvider)

  const [links] = events
  const [currentEvent, setCurrentEvent] = eventHandler
  const prevScroll = useRef(null)
  const prevEvent = useRef(currentEvent)

  const onSnapStart = useCallback(
    (index) => {
      if (currentEvent === links[index]) return
      setCurrentEvent(links[index])
    },
    [links, setCurrentEvent]
  )

  const onSnap = useCallback(() => {
    prevEvent.current = currentEvent
  }, [currentEvent])

  const _snapTo = useScrollSnap({ ...options, scrollContainerRef: contentRef, onSnapStart, onSnap })

  useLayoutEffect(() => {
    snapTo.current = _snapTo
  }, [_snapTo])

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
      const _prevIndex = links.indexOf(prevEvent.current)
      let _targetIndex = links.indexOf(currentEvent)

      if (_prevIndex === _targetIndex) {
        _targetIndex = direction === _targetIndex ? prevIndex : direction
      }

      const delta = _targetIndex - _prevIndex
      let _progress = delta === 0 ? 1 : Math.abs((scrollValue - _prevIndex) / delta)
      _progress = Math.min(1, Math.max(_progress, 0))
      onIndicatorMoveRef.current({ target: indicatorRef.current.firstChild, progress: _progress })
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
    _snapTo(currIndex, true)
    moveIndicator(1, currIndex, currIndex)
  }, [links, indicatorRef])

  const _children = useMemo(() => {
    return (
      children &&
      React.Children.map(children, (child) => {
        if (React.isValidElement(child) && child.props.__TYPE === 'Pane') {
          return React.cloneElement(child, {
            style: { ...child.props.style, ...paneStyle },
            className: [child.props.className, paneClass].join(' ').trim()
          })
        }
        return child
      })
    )
  }, [children])

  return (
    <div
      className={styles['tab-content']}
      ref={contentRef}
      onScroll={handleScroll}
      style={{
        position: 'relative',
        display: 'flex',
        flexDirection: propValues.flexDirection,
        flexGrow: '1',
        overflow: 'auto',
        WebkitOverFlowScrolling: 'auto'
      }}
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
