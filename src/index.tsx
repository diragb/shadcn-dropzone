// Packages:
import React from 'react'
import { useDropzone } from 'react-dropzone'
import { cn } from './lib/utils'

// Typescript:
import {
  type DropzoneProps as _DropzoneProps,
  type DropzoneState as _DropzoneState
} from 'react-dropzone'

export interface DropzoneState extends _DropzoneState {}

export interface DropzoneProps extends Omit<_DropzoneProps, 'children'> {
  className?: string;
  children?: (dropzone: DropzoneState) => React.ReactNode;
}

// Imports:
import { Upload } from 'lucide-react'

// Functions:
const Dropzone = ({
  className,
  children,
  ...props
}: DropzoneProps) => {
  // Constants:
  const dropzone = useDropzone(props)

  // Return:
  return (
    <div
      { ...dropzone.getRootProps() }
      className={cn('flex justify-center items-center w-full h-32 border-dashed border-2 border-gray-200 rounded-lg hover:bg-accent hover:text-accent-foreground transition-all select-none cursor-pointer', className)}
    >
      <input { ...dropzone.getInputProps() } />
      {
        children ? (
          children(dropzone)
        ) : (
          <>
            {
              dropzone.isDragAccept ? (
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
          </>
        )
      }
    </div>
  )
}

// Exports:
export default Dropzone
