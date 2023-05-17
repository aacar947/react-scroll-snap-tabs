/* eslint-disable prettier/prettier */
import React, { useState, useContext, useRef, useEffect, useLayoutEffect, useCallback } from 'react'
import PropTypes from 'prop-types'
import styles from './styles.module.css'
import { useScrollSnap } from './utilities'
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

function ScrollSnapTabs({ children, defaultKey, eventKeys, style, layout = 'vertical' }) {
  const propValues = layout === 'horizontal' ? LAYOUT_PROP_VALUES.horizontal : LAYOUT_PROP_VALUES.vertical
  const propNames = layout === 'horizontal' ? LAYOUT_PROP_NAMES.horizontal : LAYOUT_PROP_NAMES.vertical

  const [currentEvent, setCurrentEvent] = useState(defaultKey || null)
  const [events, setEvents] = useState([])
  const indicatorRef = useRef(null)
  const contentRef = useRef(null)
  const snapToRef = useRef(null)
  const linkMapRef = useRef(new Map())

  useEffect(() => {
    if (!currentEvent && events.length > 0) {
      setCurrentEvent(() => events[0])
    }
    console.log('event:', currentEvent)
  }, [events, setCurrentEvent])

  return (
    <TabProvider.Provider
      value={{
        eventHandler: [currentEvent, setCurrentEvent],
        events: [events, setEvents],
        indicatorRef,
        contentRef,
        linkMapRef,
        snapToRef,
        propValues,
        propNames,
        snapTo: snapToRef.current
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
  indicatorStyle,
  children,
  style = {},
  linkStyle = {},
  linkClass = ''
}) {
  const { indicatorRef, propValues, propNames } = useContext(TabProvider)

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

  const _children =
    children &&
    React.Children.map(children, (child) => {
      if (React.isValidElement(child)) {
        return React.cloneElement(child, {
          style: linkStyle,
          className: linkClass,
          activeClass: activeLinkClass,
          activeStyle: activeLinkStyle
        })
      }
      return child
    })

  return (
    <div
      style={{ ...style, display: 'flex', flexDirection: propValues.flexDirection, position: 'relative' }}
      className={className}
    >
      <div
        className={indicatorClass}
        style={{
          backgroundColor: indicatorColor || 'black',
          [propNames.minHeight]: '2px',
          position: 'absolute',
          bottom: propValues.indicatorBottom,
          left: propValues.indicatorLeft,
          ...indicatorStyle
        }}
        ref={indicatorRef}
      />
      {_children || (eventKeys && eventKeys.map(createNavLinks))}
    </div>
  )
}
Nav.propTypes = {
  eventKeys: PropTypes.arrayOf(PropTypes.string),
  className: PropTypes.string,
  children: PropTypes.node
}

function Link({ eventKey, className, children, style, activeStyle = { color: 'green' }, activeClass }) {
  const { eventHandler, events, linkMapRef } = useContext(TabProvider)
  const [selectedTab, setSelectedTab] = eventHandler
  const [, setEvents] = events
  const linkRef = useRef(null)
  const handleClick = (e) => {
    setSelectedTab(eventKey)
    //console.log(selectedTab)
  }

  useLayoutEffect(() => {
    className += styles['tab-link']
    setEvents((prev) => [...prev, eventKey])
    linkMapRef.current.set(eventKey, linkRef.current)
    console.log('tabs: ', linkMapRef.current)
  }, [eventKey])

  const _className =
    selectedTab === eventKey
      ? className + `${className} ${styles['tab-link']} ${activeClass}`
      : `${className} ${styles['tab-link']}`

  return (
    <div
      onClick={handleClick}
      className={_className}
      style={selectedTab === eventKey ? { ...style, ...activeStyle } : style}
      ref={linkRef}
    >
      {children || eventKey}
    </div>
  )
}

function Content({ children, style, ...rest }) {
  const { eventHandler, indicatorRef, events, linkMapRef, contentRef, snapToRef, propValues, propNames } =
    useContext(TabProvider)

  const [links] = events
  const [, setCurrentEvent] = eventHandler
  const prevScroll = useRef(null)

  const onSnapStart = useCallback(
    (index) => {
      setCurrentEvent(links[index])
    },
    [links, setCurrentEvent]
  )

  const snapTo = useScrollSnap({
    scrollContainerRef: contentRef,
    onSnapStart,
    duration: 250
  })

  useEffect(() => {
    snapToRef.current = snapTo
  }, [snapTo])

  const mapNumber = (number, numberMin, numberMax, mapFrom, mapTo) => {
    number = Math.min(numberMax, Math.max(number, numberMin))
    return ((number - numberMin) / (numberMax - numberMin)) * (mapTo - mapFrom) + mapFrom
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
    const current = linkMapRef.current.get(links[prevIndex])
    const currentLeft = (current && current[propNames.offsetLeft]) || 0
    const currentWidth = (current && current[propNames.offsetWidth]) || 0
    const target = linkMapRef.current.get(links[direction])
    const targetLeft = target && target[propNames.offsetLeft]
    const targetWidth = target && target[propNames.offsetWidth]
    const indicator = indicatorRef.current

    indicator.style[propNames.left] = mapNumber(unitScroll, 0, 1, currentLeft, targetLeft) + 'px'
    indicator.style[propNames.width] = mapNumber(unitScroll, 0, 1, currentWidth, targetWidth) + 'px'
  }

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
      {children}
    </div>
  )
}

function Pane({ children, eventKey, ...rest }) {
  const paneRef = useRef(null)
  const { eventHandler, events, snapTo } = useContext(TabProvider)
  const [currentEvent] = eventHandler
  const [links] = events

  useEffect(() => {
    if (eventKey === currentEvent) snapTo(links.indexOf(eventKey))
  })

  return (
    <div ref={paneRef} {...rest} data-scroll-snap>
      {children}
    </div>
  )
}

ScrollSnapTabs.Nav = Nav
ScrollSnapTabs.Link = Link
ScrollSnapTabs.Content = Content
ScrollSnapTabs.Pane = Pane
export default ScrollSnapTabs
