// Packages:
import React, { useState } from 'react'
import { useDropzone } from 'react-dropzone'
import { cn } from './lib/utils'
import truncate from 'truncate'

// Typescript:
import {
  type DropzoneProps as _DropzoneProps,
  type DropzoneState as _DropzoneState
} from 'react-dropzone'

export interface DropzoneState extends _DropzoneState {}

export interface DropzoneProps extends Omit<_DropzoneProps, 'children'> {
  containerClassName?: string
  dropZoneClassName?: string
  children?: (dropzone: DropzoneState) => React.ReactNode
  showFilesList?: boolean
  showErrorMessage?: boolean
}

// Functions:

const Upload = ({
  className,
}: {
  className?: string
}) => (
  <svg xmlns='http://www.w3.org/2000/svg' width='24' height='24' viewBox='0 0 24 24' fill='none' stroke='currentColor' strokeWidth='2' strokeLinecap='round' strokeLinejoin='round' className={cn('lucide lucide-upload', className)}>
    <path d='M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4'/>
    <polyline points='17 8 12 3 7 8'/>
    <line x1='12' x2='12' y1='3' y2='15'/>
  </svg>
)

const PDF = ({
  className,
}: {
  className?: string
}) => (
  <svg xmlns='http://www.w3.org/2000/svg' width='24' height='24' viewBox='0 0 24 24' fill='none' stroke='currentColor' strokeWidth='2' strokeLinecap='round' strokeLinejoin='round' className={cn('lucide lucide-file-text', className)}>
    <path d='M15 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V7Z'/>
    <path d='M14 2v4a2 2 0 0 0 2 2h4'/>
    <path d='M10 9H8'/>
    <path d='M16 13H8'/>
    <path d='M16 17H8'/>
  </svg>
)

const Image = ({
  className,
}: {
  className?: string
}) => (
  <svg xmlns='http://www.w3.org/2000/svg' width='24' height='24' viewBox='0 0 24 24' fill='none' stroke='currentColor' strokeWidth='2' strokeLinecap='round' strokeLinejoin='round' className={cn('lucide lucide-image', className)}>
    <rect width='18' height='18' x='3' y='3' rx='2' ry='2'/>
    <circle cx='9' cy='9' r='2'/>
    <path d='m21 15-3.086-3.086a2 2 0 0 0-2.828 0L6 21'/>
  </svg>
)

const Trash = ({
  className,
}: {
  className?: string
}) => (
  <svg xmlns='http://www.w3.org/2000/svg' width='24' height='24' viewBox='0 0 24 24' fill='none' stroke='currentColor' strokeWidth='2' strokeLinecap='round' strokeLinejoin='round' className={cn('lucide lucide-trash', className)}>
    <path d='M3 6h18'/>
    <path d='M19 6v14c0 1-1 2-2 2H7c-1 0-2-1-2-2V6'/>
    <path d='M8 6V4c0-1 1-2 2-2h4c1 0 2 1 2 2v2'/>
  </svg>
)

const Dropzone = ({
  containerClassName,
  dropZoneClassName,
  children,
  showFilesList = true,
  showErrorMessage = true,
  ...props
}: DropzoneProps) => {
  // Constants:
  const dropzone = useDropzone({
    ...props,
    onDrop(acceptedFiles, fileRejections, event) {
      if (props.onDrop) props.onDrop(acceptedFiles, fileRejections, event)
      else {
        setFilesUploaded(_filesUploaded => [..._filesUploaded, ...acceptedFiles ])
        if (fileRejections.length > 0) {
          let _errorMessage = `Could not upload ${ fileRejections[0].file.name }`
          if (fileRejections.length > 1) _errorMessage = _errorMessage + `, and ${ fileRejections.length - 1 } other files.`
          setErrorMessage(_errorMessage)
        } else {
          setErrorMessage('')
        }
      }
    },
  })

  // State:
  const [filesUploaded, setFilesUploaded] = useState<File[]>([])
  const [errorMessage, setErrorMessage] = useState<string>()

  // Functions:
  const deleteUploadedFile = (index: number) => {
    setFilesUploaded(_uploadedFiles => [
      ..._uploadedFiles.slice(0, index),
      ..._uploadedFiles.slice(index + 1),
    ])
  }

  // Return:
  return (
    <div
      className={cn('flex flex-col gap-2', containerClassName)}
    >
      <div
        { ...dropzone.getRootProps() }
        className={cn('flex justify-center items-center w-full h-32 border-dashed border-2 border-gray-200 rounded-lg hover:bg-accent hover:text-accent-foreground transition-all select-none cursor-pointer', dropZoneClassName)}
      >
        <input { ...dropzone.getInputProps() } />
        {
          children ? (
            children(dropzone)
          ) : dropzone.isDragAccept ? (
            <div className='text-sm font-medium'>Drop your files here!</div>
          ) : (
            <div className='flex items-center flex-col gap-1.5'>
              <div className='flex items-center flex-row gap-0.5 text-sm font-medium'>
                <Upload className='mr-2 h-4 w-4' /> Upload files
              </div>
              {
                props.maxSize && (
                  <div className='text-xs text-gray-400 font-medium'>Max. file size: { (props.maxSize / (1024 * 1024)).toFixed(2) } MB</div>
                )
              }
            </div>
          )
        }
      </div>
      { errorMessage && <span className='text-xs text-red-600 mt-3'>{ errorMessage }</span> }
      {
        (showFilesList && filesUploaded.length > 0) && (
          <div className={`flex flex-col gap-2 w-full ${ filesUploaded.length > 2 ? 'h-48' : 'h-fit' } mt-2 ${ filesUploaded.length > 0 ? 'pb-2' : '' }`}>
            <div className='w-full'>
              {
                filesUploaded.map((fileUploaded, index) => (
                  <div key={index} className='flex justify-between items-center flex-row w-full h-16 mt-2 px-4 border-solid border-2 border-gray-200 rounded-lg shadow-sm'>
                    <div className='flex items-center flex-row gap-4 h-full'>
                      {
                        fileUploaded.type === 'application/pdf' ? (
                          <PDF className='text-rose-700 w-6 h-6' />
                        ) : (
                          <Image className='text-rose-700 w-6 h-6' />
                        )
                      }
                      <div className='flex flex-col gap-0'>
                        <div className='text-[0.85rem] font-medium leading-snug'>{ truncate(fileUploaded.name.split('.').slice(0, -1).join('.'), 30) }</div>
                        <div className='text-[0.7rem] text-gray-500 leading-tight'>.{ fileUploaded.name.split('.').pop() } • { (fileUploaded.size / (1024 * 1024)).toFixed(2) } MB</div>
                      </div>
                    </div>
                    <div
                      className='p-2 rounded-full border-solid border-2 border-gray-100 shadow-sm hover:bg-accent transition-all select-none cursor-pointer'
                      onClick={() => deleteUploadedFile(index)}
                    >
                      <Trash className='w-4 h-4' />
                    </div>
                  </div>
                ))
              }
            </div>
          </div>
        )
      }
    </div>
  )
}

// Exports:
export default Dropzone
