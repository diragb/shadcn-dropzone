import React from 'react';
import { type DropzoneProps as _DropzoneProps, type DropzoneState as _DropzoneState } from 'react-dropzone';
export interface DropzoneState extends _DropzoneState {
}
export interface DropzoneProps extends Omit<_DropzoneProps, 'children'> {
    className?: string;
    children?: (dropzone: DropzoneState) => React.ReactNode;
}
declare const Dropzone: ({ className, children, ...props }: DropzoneProps) => React.JSX.Element;
export default Dropzone;
