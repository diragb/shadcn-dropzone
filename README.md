# Shadcn Dropzone

[![npm](https://img.shields.io/badge/npm-shadcn--dropzone-brightgreen.svg?style=flat-square)](https://www.npmjs.com/package/shadcn-dropzone)
[![npm version](https://img.shields.io/npm/v/shadcn-dropzone.svg?style=flat-square)](https://www.npmjs.com/package/shadcn-dropzone)
[![npm downloads](https://img.shields.io/npm/dm/shadcn-dropzone.svg?style=flat-square)](https://www.npmjs.com/package/shadcn-dropzone)
[![sponsors](https://img.shields.io/github/sponsors/diragb)](https://github.com/sponsors/diragb)

Ready to use File Upload Dropzone component, built with **[shadcn/ui](http://ui.shadcn.com)** and **[react-dropzone](https://www.npmjs.com/package/react-dropzone)**.

**Demo:** https://diragb.github.io/shadcn-dropzone

## Installation

```bash
npm install --save shadcn-dropzone
```

or

```bash
yarn add shadcn-dropzone
```

## Usage

```tsx
import Dropzone from 'shadcn-dropzone';

// Use the default UI
const DefaultUI = () => {
  return (
    <Dropzone
      onDrop={(acceptedFiles: File) => {
        // Do something with the files
      }}
    />
  );
}

// Or, pass a custom UI
const CustomUI = () => {
  return (
    <Dropzone
      onDrop={(acceptedFiles: File) => {
        // Do something with the files
      }}
    >
      {(dropzone: DropzoneState) => (
        <>
          {
            dropzone.isDragAccept ? (
              <div className='text-sm font-medium'>Drop your files here!</div>
            ) : (
              <div className='flex items-center flex-col gap-1.5'>
                <div className='flex items-center flex-row gap-0.5 text-sm font-medium'>
                  Upload files
                </div>
              </div>
            )
          }
          <div className='text-xs text-gray-400 font-medium'>
            { dropzone.acceptedFiles.length } files uploaded so far.
          </div>
        </>
      )}
    </Dropzone>
  )
}
```

Make sure you have TailwindCSS set up in your project, as this component relies on them.

## Props

Check out [react-dropzone](https://www.npmjs.com/package/react-dropzone) for all the props.

## License
MIT