import type { Metadata } from "next";
import "@/components/ti-calculator.css";
import { CountClient } from "./CountClient";

export const metadata: Metadata = {
  title: "Count to n — EML and One",
};

export default function Page() {
  return (
    <>
      <script dangerouslySetInnerHTML={{ __html: "document.documentElement.dataset.countHash=location.hash" }} />
      <CountClient />
    </>
  );
}
