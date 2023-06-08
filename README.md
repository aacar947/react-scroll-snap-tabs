# React Scroll Snap Tabs

> The React Scroll Snap Tabs Component for React.js is a versatile and interactive component designed to provide a seamless tab navigation experience, specifically optimized for touch devices. With its intuitive touch gestures and responsive design, this component ensures effortless scrolling and tab switching on mobile devices and tablets. Users can easily swipe between tabs, making it a breeze to navigate through the content. The component is thoughtfully designed to accommodate the unique interaction patterns of touch devices, offering a user-friendly experience for both touch and non-touch environments. Developers can seamlessly integrate this touch-friendly component into their React.js applications, providing a consistent and enjoyable tabbed interface across all devices.

[![NPM](https://img.shields.io/npm/v/react-scroll-snap-tabs.svg)](https://www.npmjs.com/package/react-scroll-snap-tabs) [![JavaScript Style Guide](https://img.shields.io/badge/code_style-standard-brightgreen.svg)](https://standardjs.com)

## Table Of Contents

1. [Install](#install)
1. [Basic Usage](#basic-usage)
1. [Advanced Usage](#advanced-usage)
1. [Props](#props)
1. [Nav Component Props](#nav-component-props)
1. [Link Component Props](#link-component-props)
1. [Content Component Props](#content-component-props)
1. [Pane Component Props](#pane-component-props)
1. [Easing Function](#easing-function)
1. [onIndicatorMove Event](#onindicatormove-event)
1. [How Indicator Works](#how-indicator-works)

## Install

```bash
npm install --save react-scroll-snap-tabs
```

## Basic Usage

Note that, in order to prevent unexpected behaviors, the order of links and panes should exactly match based on their eventKeys.

```jsx
import React, { Component } from 'react'

import Tabs from 'react-scroll-snap-tabs'
import 'react-scroll-snap-tabs/dist/index.css'

const App = () => {
  return (
    <div style={{ width: '400px', height: '100vh', border: '1px solid gray' }}>
      <Tabs eventKeys={['Tab 1', 'Tab 2']}>
        <Tabs.Content paneStyle={{ border: '1px solid gray' }}>
          <Tabs.Pane eventKey='Tab 1'>Content 1</Tabs.Pane>
          <Tabs.Pane eventKey='Tab 2'>Content 2</Tabs.Pane>
        </Tabs.Content>
      </Tabs>
    </div>
  )
}

export default App
```

Result:

![BasicScrollSnapTabs2](https://github.com/aacar947/react-scroll-snap-tabs/assets/90392197/ca7b7508-c7f3-421f-a513-15a69884f9bc)

## Advanced Usage

```jsx
import React, { Component } from 'react'

import Tabs from 'react-scroll-snap-tabs'
import 'react-scroll-snap-tabs/dist/index.css'

const App = () => {
  const width = 10
  const onIndicatorMove = (e) => {
    const indicator = e.target
    const timing = (t) => -12 * (t - 0.5) * (t - 0.5) + 4
    const progress = timing(e.progress)
    indicator.style.width = progress * width + 'px'
  }

  return (
    <div style={{ width: '400px', height: '100vh', backgroundColor: '#333' }}>
      <Tabs
        style={{ borderRight: '1px solid gray' }}
        snapDuration={250}
        easing='ease-in-out'
        indicatorSize='20px'
        defaultKey='tab3'
      >
        <Tabs.Nav
          activeLinkStyle={{ color: 'white' }}
          linkStyle={{ whiteSpace: 'nowrap' }}
          indicatorStyle={{
            borderRadius: '3px',
            width: width + 'px',
            maxWidth: '100%',
            backgroundColor: 'orange'
          }}
          style={{ color: 'gray', backgroundColor: 'black', borderRadius: '5px' }}
          onIndicatorMove={onIndicatorMove}
          className='tab-nav'
        >
          <Tabs.Link eventKey='tab1'>Tab 1</Tabs.Link>
          <Tabs.Link eventKey='tab2'>Very Long Tab 2</Tabs.Link>
          <Tabs.Link eventKey='tab3'>Tab 3</Tabs.Link>
          <Tabs.Link eventKey='tab4'>Very Long Tab 4</Tabs.Link>
          <Tabs.Link eventKey='tab5'>Very Long Tab 5</Tabs.Link>
        </Tabs.Nav>
        <Tabs.Content
          style={{ overscrollBehaviorY: 'contain' }}
          paneStyle={{ minHeight: '100%', minWidth: '100%' }}
        >
          <Tabs.Pane eventKey='tab1'>
            <CustomComponent color='white'>Content 1</CustomComponent>
          </Tabs.Pane>
          <Tabs.Pane eventKey='tab2'>
            <CustomComponent color='white'>Content 2</CustomComponent>
          </Tabs.Pane>
          <Tabs.Pane eventKey='tab3'>
            <CustomComponent color='white'>Content 3</CustomComponent>
          </Tabs.Pane>
          <Tabs.Pane eventKey='tab4'>
            <CustomComponent color='white'>Content 4</CustomComponent>
          </Tabs.Pane>
          <Tabs.Pane eventKey='tab5'>
            <CustomComponent color='white'>Content 5</CustomComponent>
          </Tabs.Pane>
        </Tabs.Content>
      </Tabs>
    </div>
  )
}

function CustomComponent({ children, color }) {
  return (
    <div
      style={{
        backgroundColor: 'transparent',
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
        fontStyle: 'bold',
        fontSize: '3vw',
        width: '100%',
        height: '100%',
        color
      }}
    >
      {children}
    </div>
  )
}

export default App
```

Result:

![AdvancedScrollSnapTabs](https://github.com/aacar947/react-scroll-snap-tabs/assets/90392197/23f28a1f-d89e-4c81-b728-ea2008a74ffd)

## Props

| Name                   | Type             | Default            | Description                                                                                                                                                                                                                                                                    |
| :--------------------- | :--------------- | :----------------- | :----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| activeLinkClass        | string           |                    | Class name to be applied to the active link in the navigation.                                                                                                                                                                                                                 |
| activeLinkStyle        | object           | {color: '#5A90E4'} | Style to be applied to the active link in the navigation.                                                                                                                                                                                                                      |
| defaultKey             | string(eventKey) | first tab's event  | default event key to snap to the corresponding tab on load                                                                                                                                                                                                                     |
| easing                 | string \| func   | "ease-out"         | Sets the easing function for snap animation. The value should be either "ease-in", "ease-out", or "ease-in-out". If a random string value is provided, the default easing function will be (t) => t (linear). [read more](#easing-function)                                    |
| eventKeys              | [string]         |                    | Manually configure and customize all events without the need for a Nav component                                                                                                                                                                                               |
| indicatorClass         | string           |                    | Assigns a class name to the indicator element.                                                                                                                                                                                                                                 |
| indicatorColor         | string           | "black"            | Assigns the background color of the indicator element.                                                                                                                                                                                                                         |
| indicatorSize          | string           | "100%"             | Assigns the size of the indicator element.                                                                                                                                                                                                                                     |
| indicatorStyle         | object           |                    | Style to be applied to the indicator element                                                                                                                                                                                                                                   |
| indicatorParentClass   | string           |                    | Assigns a class name to the indicator's parent element.                                                                                                                                                                                                                        |
| indicatorParentStyle   | object           |                    | Style to be applied to the indicator's parent element                                                                                                                                                                                                                          |
| layout                 | string           | "veritical"        | Sets the layout of the component. The value should be either "horizontal" or "vertical". If a random string value is provided, the default layout will be "vertical"                                                                                                           |
| linkClass              | string           |                    | Assigns a class name to all of the link components in the navigation component.                                                                                                                                                                                                |
| linkStyle              | object           |                    | Applies styles to all of the link components in the navigation component.                                                                                                                                                                                                      |
| onIndicatorMove        | func             |                    | When the indicator element moves, the onIndicatorMove callback function is triggered along with the movement.                                                                                                                                                                  |
| scrollIntoViewEasing   | string \| func   | "ease-out"         | Sets the easing function for scroll into view animation. The value should be either "ease-in", "ease-out", or "ease-in-out". If a random string value is provided, the default easing function will be (t) => t (linear). [read more](#easing-function)                        |
| scrollIntoViewDuration | number           | 250                | Sets the duration in ms for the scroll into view animation.                                                                                                                                                                                                                    |
| scrollIntoViewOffset   | number           | 100                | Sets an additional scroll offset for the scroll into view animation.                                                                                                                                                                                                           |
| snapDuration           | number           | 250                | Sets the duration in ms for the scroll snap animation.                                                                                                                                                                                                                         |
| snapThreshold          | number           | 30                 | Sets the threshold for the snap action to start. If the threshold value is exceeded, it snaps to the next item; otherwise, it snaps to the current item.                                                                                                                       |
| swipeThreshold         | number           | 200                | Sets the threshold for the snap action to start on touch devices. When a swipe action is performed, the algorithm calculates an inertial value. If the calculated value exceeds the swipe threshold value, it snaps to the next item; otherwise, it snaps to the current item. |

## Nav Component Props

In the navigation component, you can utilize the same props as described previously, which are as follows:

- activeLinkClass
- activeLinkStyle
- eventKeys
- indicatorClass
- indicatorColor
- indicatorSize
- indicatorStyle
- indicatorParentClass
- indicatorParentStyle
- linkStyle
- linkClass
- onIndicatorMove
- scrollIntoViewEasing
- scrollIntoViewDuration
- scrollIntoViewOffset

## Link Component Props

| Name        | Type   | Default | Description                                                                     |
| :---------- | :----- | :------ | :------------------------------------------------------------------------------ |
| activeClass | string |         | The class name to be applied to the link when it's active.                      |
| activeStyle | object |         | The style to be applied to the link when it is active.                          |
| eventKey    | string |         | The event name that corresponds to the pane component with the same event name. |

## Content Component Props

| Name      | Type   | Default | Description                                                                  |
| :-------- | :----- | :------ | :--------------------------------------------------------------------------- |
| paneClass | string |         | Assigns a class name to all of the pane components in the content component. |
| paneStyle | object |         | Applies styles to all of the pane components in the content component.       |

## Pane Component Props

| Name     | Type   | Default | Description                                                                     |
| :------- | :----- | :------ | :------------------------------------------------------------------------------ |
| eventKey | string |         | The event name that corresponds to the link component with the same event name. |

## Easing Function

You can use predefined easing functions by providing either "ease-in", "ease-out", or "ease-in-out" string values. If a random string value is provided, the default easing function will be (t) => t (linear). Alternatively, you can provide your own easing function that accepts a number argument between 0 and 1 and returns a number between 0 and 1. You can find more about easing functions on [easings.net](https://easings.net/#).

## onIndicatorMove Event

When the indicator element moves, the onIndicatorMove callback function is triggered along with the movement.

### Event Properties:

### `Event.progress`

It is a fractional value between two snap points that ranges from 0 to 1. The current snap point, representing the current content, is 0, and the target snap point is 1.

### `Event.target`

Returns the indicator element.

### `Event.isInteracting`

Returns a boolean value indicating whether or not the user is interacting with the content area.

### Example

```jsx
import React, { Component } from 'react'

import Tabs from 'react-scroll-snap-tabs'
import 'react-scroll-snap-tabs/dist/index.css'

const App = () => {
  const width = 10
  const onIndicatorMove = (e) => {
    const indicator = e.target
    const timing = (t) => -12 * (t - 0.5) * (t - 0.5) + 4
    const progress = timing(e.progress)
    indicator.style.width = progress * width + 'px'
  }

  return (
    <div style={{ width: '400px', height: '100vh' }}>
      <Tabs
        style={{ borderRight: '1px solid gray' }}
        snapDuration={250}
        easing='ease-in-out'
        indicatorSize='20px'
        defaultKey='tab3'
        onIndicatorMove={onIndicatorMove}
      >
        <Tabs.Nav
          activeLinkStyle={{ color: '#23527C', backgroundColor: 'ghostwhite' }}
          indicatorStyle={{
            borderRadius: '3px',
            width: width + 'px',
            maxWidth: '100%',
            zIndex: 999,
            backgroundColor: '#333'
          }}
          linkStyle={{ whiteSpace: 'nowrap' }}
          style={{ color: 'gray' }}
          className='tab-nav'
        >
          <Tabs.Link eventKey='tab1'>Tab 1</Tabs.Link>
          <Tabs.Link eventKey='tab2'>Tab 2</Tabs.Link>
          <Tabs.Link eventKey='tab3'>Long Tab Name 3</Tabs.Link>
        </Tabs.Nav>
        <Tabs.Content
          style={{ overscrollBehaviorY: 'contain' }}
          paneStyle={{ minHeight: '100%', minWidth: '100%' }}
        >
          <Tabs.Pane eventKey='tab1'>
            <CustomComponent color='#B3C890'>Content 1</CustomComponent>
          </Tabs.Pane>
          <Tabs.Pane eventKey='tab2'>
            <CustomComponent color='#73A9AD'>Content 2</CustomComponent>
          </Tabs.Pane>
          <Tabs.Pane eventKey='tab3'>
            <CustomComponent color='#F5F0BB'>Content 3</CustomComponent>
          </Tabs.Pane>
        </Tabs.Content>
      </Tabs>
    </div>
  )
}

export default App
```

## How Indicator Works

When the user scrolls through the content area, if the layout is 'vertical', the indicator parent adjusts its left and width values to align with the target link element's left and width values. If the layout is 'horizontal', it aligns its top and height values.

To provide a visual representation of this behavior, consider the following HTML code, which showcases a rendered indicator parent and indicator elements in a vertical layout application:

```html
<div
  class="indicator-parent"
  style="position: absolute; bottom: 0px; border: 1px solid red; left: 53px; width: 128px;"
>
  <div
    class="indicator"
    style="height: 100%; margin: auto; min-height: 3px; background-color: black; max-width: 75%;"
  ></div>
</div>
```

![IndicatorScrollSnapTabs2](https://github.com/aacar947/react-scroll-snap-tabs/assets/90392197/c4802e76-efa1-456c-aabe-9cfbf9ff3e0a)

In the provided code, the indicator parent element is represented by the \<div> with the class name 'indicator-parent'. It is positioned absolutely and has a red border. Its left and width values are adjusted dynamically based on the corresponding link element's left and width values.

Inside the indicator parent, the indicator element is represented by the \<div> with the class name 'indicator'. The background color is black.

## License

MIT © [aacar947](https://github.com/aacar947)
